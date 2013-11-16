// NOTE: This package has been changed and merged into Go's standard library.
// Please consider to use tip of Go's source code if you want to use
// RSASSA-PSS.
package pss

import (
	"crypto"
	"crypto/rsa"

	"errors"
	"hash"
	"io"
	"math/big"
)

func emsaPSSEncode(mHash []byte, emBits int, salt []byte, hash hash.Hash) ([]byte, error) {
	hLen := hash.Size()
	sLen := len(salt)
	emLen := (emBits + 7) / 8

	// 1.  If the length of M is greater than the input limitation for the
	//     hash function (2^61 - 1 octets for SHA-1), output "message too
	//     long" and stop.
	//
	// 2.  Let mHash = Hash(M), an octet string of length hLen.

	if len(mHash) != hLen {
		return nil, errors.New("crypto/rsa: input must be hashed message")
	}

	// 3.  If emLen < hLen + sLen + 2, output "encoding error" and stop.

	if emLen < hLen+sLen+2 {
		return nil, errors.New("crypto/rsa: encoding error")
	}

	em := make([]byte, emLen)
	db := em[:emLen-sLen-hLen-2+1+sLen]
	h := em[emLen-sLen-hLen-2+1+sLen : emLen-1]

	// 4.  Generate a random octet string salt of length sLen; if sLen = 0,
	//     then salt is the empty string.
	//
	// 5.  Let
	//       M' = (0x)00 00 00 00 00 00 00 00 || mHash || salt;
	//
	//     M' is an octet string of length 8 + hLen + sLen with eight
	//     initial zero octets.
	//
	// 6.  Let H = Hash(M'), an octet string of length hLen.

	prefix := []byte{0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00}

	hash.Write(prefix[0:8])
	hash.Write(mHash)
	hash.Write(salt)

	h = hash.Sum(h[:0])
	hash.Reset()

	// 7.  Generate an octet string PS consisting of emLen - sLen - hLen - 2
	//     zero octets.  The length of PS may be 0.
	//
	// 8.  Let DB = PS || 0x01 || salt; DB is an octet string of length
	//     emLen - hLen - 1.

	db[emLen-sLen-hLen-2] = 0x01
	copy(db[emLen-sLen-hLen-1:], salt)

	// 9.  Let dbMask = MGF(H, emLen - hLen - 1).
	//
	// 10. Let maskedDB = DB \xor dbMask.

	mgf1XOR(db, hash, h)

	// 11. Set the leftmost 8emLen - emBits bits of the leftmost octet in
	//     maskedDB to zero.

	db[0] &= (0xFF >> uint(8*emLen-emBits))

	// 12. Let EM = maskedDB || H || 0xbc.
	em[emLen-1] = 0xBC

	// 13. Output EM.
	return em, nil
}

func emsaPSSVerify(mHash []byte, em []byte, emBits, sLen int, hash hash.Hash) error {
	// 1.  If the length of M is greater than the input limitation for the
	//     hash function (2^61 - 1 octets for SHA-1), output "inconsistent"
	//     and stop.
	//
	// 2.  Let mHash = Hash(M), an octet string of length hLen.
	hLen := hash.Size()
	if hLen != len(mHash) {
		return rsa.ErrVerification
	}

	// 3.  If emLen < hLen + sLen + 2, output "inconsistent" and stop.
	emLen := (emBits + 7) / 8
	if emLen < hLen+sLen+2 {
		return rsa.ErrVerification
	}

	// 4.  If the rightmost octet of EM does not have hexadecimal value
	//     0xbc, output "inconsistent" and stop.
	if em[len(em)-1] != 0xBC {
		return rsa.ErrVerification
	}

	// 5.  Let maskedDB be the leftmost emLen - hLen - 1 octets of EM, and
	//     let H be the next hLen octets.
	db := em[:emLen-hLen-1]
	h := em[emLen-hLen-1 : len(em)-1]

	// 6.  If the leftmost 8emLen - emBits bits of the leftmost octet in
	//     maskedDB are not all equal to zero, output "inconsistent" and
	//     stop.
	if em[0]&(0xFF<<uint(8-(8*emLen-emBits))) != 0 {
		return rsa.ErrVerification
	}

	// 7.  Let dbMask = MGF(H, emLen - hLen - 1).
	//
	// 8.  Let DB = maskedDB \xor dbMask.
	mgf1XOR(db, hash, h)

	// 9.  Set the leftmost 8emLen - emBits bits of the leftmost octet in DB
	//     to zero.
	db[0] &= (0xFF >> uint(8*emLen-emBits))

	// 10. If the emLen - hLen - sLen - 2 leftmost octets of DB are not zero
	//     or if the octet at position emLen - hLen - sLen - 1 (the leftmost
	//     position is "position 1") does not have hexadecimal value 0x01,
	//     output "inconsistent" and stop.
	for _, e := range db[:emLen-hLen-sLen-2] {
		if e != 0x00 {
			return rsa.ErrVerification
		}
	}
	if db[emLen-hLen-sLen-2] != 0x01 {
		return rsa.ErrVerification
	}

	// 11.  Let salt be the last sLen octets of DB.
	salt := db[len(db)-sLen:]

	// 12.  Let
	//          M' = (0x)00 00 00 00 00 00 00 00 || mHash || salt ;
	//     M' is an octet string of length 8 + hLen + sLen with eight
	//     initial zero octets.
	//
	// 13. Let H' = Hash(M'), an octet string of length hLen.
	prefix := []byte{0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00}
	hash.Write(prefix)
	hash.Write(mHash)
	hash.Write(salt)

	h0 := make([]byte, hLen)
	h0 = hash.Sum(h0[:0])

	// 14. If H = H', output "consistent." Otherwise, output "inconsistent."
	for i, e := range h0 {
		if e != h[i] {
			return rsa.ErrVerification
		}
	}
	return nil
}

// SignPSS calculates the signature of hashed using RSASSA-PSS from RFC 3447 Section 8.1.
// Note that hashed must be the result of hashing the input message using the given hash funcion.
// salt is a random sequence of bytes whose length will be later used to verify the signature.
func SignPSS(rand io.Reader, priv *rsa.PrivateKey, hash crypto.Hash, hashed []byte, salt []byte) (s []byte, err error) {
	em, err := emsaPSSEncode(hashed, priv.N.BitLen()-1, salt, hash.New())
	if err != nil {
		return
	}
	m := new(big.Int).SetBytes(em)
	c, err := decrypt(rand, priv, m)
	if err != nil {
		return
	}
	s = make([]byte, (priv.N.BitLen()+7)/8)
	copyWithLeftPad(s, c.Bytes())
	return
}

// VerifyPSS verifies an RSASSA-PSS signature.
// hashed is the result of hashing the input message using the given hash function and sig is the signature.
// A valid signature is indicated by returning a nil error.
// sLen is number of bytes of the salt used to sign the message.
func VerifyPSS(pub *rsa.PublicKey, hash crypto.Hash, hashed []byte, sig []byte, sLen int) error {
	s := new(big.Int).SetBytes(sig)
	m := encrypt(new(big.Int), pub, s)
	emBits := pub.N.BitLen() - 1
	emLen := (emBits + 7) / 8
	if emLen < len(m.Bytes()) {
		return rsa.ErrVerification
	}
	em := make([]byte, emLen)
	copyWithLeftPad(em, m.Bytes())
	err := emsaPSSVerify(hashed, em, pub.N.BitLen()-1, sLen, hash.New())
	if err != nil {
		return err
	}
	return nil
}
