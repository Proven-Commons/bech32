// The Go oracle for tests/run_tests.py: the bech32 package of
// github.com/btcsuite/btcd/btcutil, at the version go.mod pins.
//
// Each line of standard input is one request, with fields in hex as
// for `bech32 serve` (`-` for an empty field):
//
//	d STRING                   bech32.DecodeGeneric
//	e VARIANT HRP VALUES       bech32.Encode (bech32) or EncodeM (bech32m)
//
// Each answer is `OK VARIANT HRP VALUES` for a decoding, `OK STRING`
// for an encoding, `FAIL` and the library's error with its spaces
// replaced, or `error` for a line this program cannot read.
package main

import (
	"bufio"
	"encoding/hex"
	"fmt"
	"io"
	"os"
	"strconv"
	"strings"

	"github.com/btcsuite/btcd/btcutil/bech32"
)

func field(f string) ([]byte, bool) {
	if f == "-" {
		return []byte{}, true
	}
	if f == "" {
		return nil, false
	}
	b, err := hex.DecodeString(f)
	return b, err == nil
}

func toField(b []byte) string {
	if len(b) == 0 {
		return "-"
	}
	return hex.EncodeToString(b)
}

// fail gives the library's error on one line: quoted, with no spaces.
func fail(err error) string {
	return "FAIL " + strings.ReplaceAll(strconv.QuoteToASCII(err.Error()), " ", "_")
}

func answer(line string) string {
	parts := strings.Split(line, " ")
	switch {
	case len(parts) == 2 && parts[0] == "d":
		s, ok := field(parts[1])
		if !ok {
			return "error"
		}
		hrp, data, version, err := bech32.DecodeGeneric(string(s))
		if err != nil {
			return fail(err)
		}
		name := "bech32"
		switch version {
		case bech32.Version0:
		case bech32.VersionM:
			name = "bech32m"
		default:
			return "FAIL unknown_version"
		}
		return fmt.Sprintf("OK %s %s %s", name, toField([]byte(hrp)), toField(data))
	case len(parts) == 4 && parts[0] == "e":
		hrp, ok1 := field(parts[2])
		data, ok2 := field(parts[3])
		if !ok1 || !ok2 {
			return "error"
		}
		var s string
		var err error
		switch parts[1] {
		case "bech32":
			s, err = bech32.Encode(string(hrp), data)
		case "bech32m":
			s, err = bech32.EncodeM(string(hrp), data)
		default:
			return "error"
		}
		if err != nil {
			return fail(err)
		}
		return "OK " + toField([]byte(s))
	}
	return "error"
}

func main() {
	in := bufio.NewReaderSize(os.Stdin, 1<<20)
	out := bufio.NewWriterSize(os.Stdout, 1<<20)
	defer out.Flush()
	for {
		line, err := in.ReadString('\n')
		if len(line) > 0 {
			fmt.Fprintln(out, answer(strings.TrimRight(line, "\r\n")))
		}
		if err == io.EOF {
			return
		}
		if err != nil {
			fmt.Fprintln(os.Stderr, err)
			os.Exit(1)
		}
	}
}
