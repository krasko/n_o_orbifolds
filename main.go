package main

import (
	"flag"
	"fmt"
	"io/ioutil"
	"math/big"
	"os"
	"path"
	"sort"
	"strconv"
	"strings"
)

var (
	stPeriod = flag.Int("p_k_period", 40, "Orbifolds for projective plane and Klein Bottle will be generated up to this period.")
	maxG     = flag.Int("max_g", 15, "Max number of crosscaps.")
	big0     = big.NewInt(0)
	big1     = big.NewInt(1)
)

// divisors is a cache for Divisors function
var divisors [][]int

// Divisors returns a slice of positive divisors of a positive integer n
func Divisors(n int) []int {
	for len(divisors) <= n {
		divisors = append(divisors, nil)
	}
	if divisors[n] == nil {
		for j := 1; j*j <= n; j++ {
			if n%j != 0 {
				continue
			}
			divisors[n] = append(divisors[n], j)
			if j*j != n {
				divisors[n] = append(divisors[n], n/j)
			}
		}
		sort.Ints(divisors[n])
	}
	return divisors[n]
}

// j is a cache for J function
var j [][]*big.Int

// J is the k-th Jordan's totient function of n
func J(k, n int) *big.Int {
	for len(j) <= k {
		j = append(j, nil)
	}
	for len(j[k]) <= n {
		j[k] = append(j[k], nil)
	}
	if j[k][n] == nil {
		bigK := big.NewInt(int64(k))
		bigN := big.NewInt(int64(n))
		j[k][n] = new(big.Int).Exp(bigN, bigK, big0)
		for _, p := range Divisors(n) {
			if len(Divisors(p)) != 2 {
				continue
			}
			bigP := big.NewInt(int64(p))
			bigPK := new(big.Int).Exp(bigP, bigK, big0)
			j[k][n].Div(j[k][n], bigPK)
			j[k][n].Mul(j[k][n], new(big.Int).Sub(bigPK, big1))
		}
	}
	return j[k][n]
}

// Phi is the Euler's function of n
func Phi(n int) *big.Int {
	return J(1, n)
}

// covering is a signature of a periodic covering of a surface
// by an orientable surface without a boundary arising from
// an orientation-reversing automorphism
type covering struct {
	Chi, L, chi, h int
	orientable     bool
	m              []int
}

// Sign returns "+" if the covered surface is orientable and "-" otherwise
func (c *covering) Sign() string {
	if !c.orientable {
		return "-"
	}
	return "+"
}

// lcm computes the least common multiple of given integers
func lcm(xs ...int) int {
	lcm := 1
	for _, x := range xs {
		var d int
		for _, i := range Divisors(x) {
			if lcm%i == 0 {
				d = i
			}
		}
		lcm = lcm * x / d
	}
	return lcm
}

// halfSumInv computes the value of
// 1/2x_1 + 1/2x_2 + ... + 1/2x_k) and simplifies the resulting fraction.
func halfSumInv(xs ...int) (numer, denom int) {
	denom = 1
	for _, x := range xs {
		numer = numer*2*x + denom
		denom *= 2 * x
		lcm := lcm(numer, denom)
		numer, denom = lcm/denom, lcm/numer
	}
	return numer, denom
}

func (c *covering) Epi() *big.Int {
	res := new(big.Int)
	m := lcm(c.m...)
	switch {
	case c.orientable && c.h == 0:
	case !c.orientable && 2-c.h == c.chi:
	case c.orientable && (c.h+c.chi)%2 != 0:
	case c.h == 0 && c.L%2 == 1: // non-orientable; no boundary; odd L
		res.Add(res, big1)
		res.Mul(res, J(1-c.chi, c.L/m))
		res.Mul(res, new(big.Int).Exp(big.NewInt(int64(m)), big.NewInt(int64(1-c.chi)), big0))
	case c.h == 0 && c.L%2 == 0: // non-orientable; no boundary; even L
		neg, pos := new(big.Int), new(big.Int)
		if c.L%4 != 0 && (c.L/2)%m == 0 {
			neg.Add(neg, big1)
			neg.Mul(neg, J(1-c.chi, c.L/2/m))
			neg.Mul(neg, new(big.Int).Exp(big.NewInt(int64(m)), big.NewInt(int64(1-c.chi)), big0))
		}
		_, b := halfSumInv(c.m...)
		if m := lcm(2, m, b); c.L%m == 0 {
			pos.Add(big1, big1)
			pos.Mul(pos, J(1-c.chi, c.L/m))
			pos.Mul(pos, new(big.Int).Exp(big.NewInt(int64(m)), big.NewInt(int64(1-c.chi)), big0))
		}
		res.Sub(pos, neg)
	case c.h > 0 && c.L%2 == 0: // with boundary
		m := lcm(2, m)
		res.Add(res, big1)
		res.Mul(res, J(1-c.chi, c.L/m))
		res.Mul(res, new(big.Int).Exp(big.NewInt(int64(m)), big.NewInt(int64(1-c.chi)), big0))
	}
	for _, m := range c.m {
		res.Mul(res, Phi(m))
	}
	return res
}

// String returns a machine-and-human-readable representation of the signature
// together with the value of EpiPlus.
func (c *covering) String() string {
	return fmt.Sprintf("%3d %3d [%s] %3d %2d %v %s", c.Chi, c.L, c.Sign(), c.chi, c.h, c.m, c.Epi())
}

// NOCoverings iterates over all coverings with period L of surfaces with
// Euler characteristic chi by Euler Characteristic Chi surfaces without a boundary
// and calls f for each covering with a non-zero number of
// order-preserving epimorphisms.
// "rem" and "m" parameters are used in recursive calls to track
// the enumeration of branch points.
// Initially "rem" should be equal to L*chi-Chi, "m" should be empty.
func NOCoverings(Chi, chi, L, rem int, f func(covering), m ...int) {
	if rem < 0 {
		return
	}
	if rem == 0 {
		mc := make([]int, len(m))
		copy(mc, m)
		for _, orientable := range []bool{true, false} {
			for h := 0; h <= 2-chi; h++ {
				cov := covering{Chi: Chi, L: L, m: mc, orientable: orientable, h: h, chi: chi}
				if cov.Epi().Cmp(big0) != 0 {
					f(cov)
				}
			}
		}
		return
	}
	next := 2
	if len(m) > 0 {
		next = m[len(m)-1]
	}
	for _, d := range Divisors(L) {
		if d < next {
			continue
		}
		NOCoverings(Chi, chi, L, rem-L+L/d, f, append(m, d)...)
	}
}

// parse parses a description of an orbifold produced by o_r_orbifolds program.
func parse(s string) (g int, k string, epi int) {
	s = strings.TrimSpace(s)
	i := strings.IndexByte(s, ' ')
  j := strings.LastIndexByte(s, ' ')
	k = strings.TrimSpace(s[i:j])
	g, err := strconv.Atoi(strings.TrimSpace(s[:i]))
	if err != nil {
		fmt.Println(err)
		os.Exit(1)
	}
	epi, err = strconv.Atoi(strings.TrimSpace(s[j:]))
	if err != nil {
		fmt.Println(err)
		os.Exit(1)
	}
	return g, k, epi
}

// readOROrbifolds reads orbifolds that arise from orientation-reversing
// automorphisms of orientable surfaces from the file "o_r_orbifolds.txt".
func readOROrbifolds() map[int]map[string]int {
	wd, err := os.Getwd()
	if err != nil {
		fmt.Println(err)
		os.Exit(1)
	}
	data, err := ioutil.ReadFile(path.Join(wd, "o_r_orbifolds.txt"))
	if err != nil {
		fmt.Println(err)
		os.Exit(1)
	}
	m := map[int]map[string]int{}
	for _, ln := range strings.Split(string(data), "\n") {
		if strings.TrimSpace(ln) == "" || ln[:1] == "#" {
			continue
		}
		g, key, epi := parse(ln)
		if m[g] == nil {
			m[g] = map[string]int{}
		}
		m[g][key] = epi
	}
	return m
}

func main() {
	m := readOROrbifolds()
	fmt.Println(`# Format: Chi L [O] chi H [m1 ... mr] E E+, where:
#
# Chi: Euler characteristics of the covering surface.
# L: Cyclic covering period.
# O: Sign, "+" for orientable orbifolds and "-" for non-orientable ones.
# chi: Euler characteristics of the covered surface.
# H: Number of boundary components in the covered surface. If O is "-", the number of crosscaps is 2 - chi - H; is O is "+", the number of handles is (2 - chi - H) / 2.
# [m1 ... mr]: Branch point indices.
# E: Number of order-preserving epimorphisms from the NEC group of the orbifold onto Z_L.
# E+: Number of order-and-orientation-preserving epimorphisms from the NEC group of the orbifold onto Z_L endowed with non-trivial sign structure.
`)
	for Chi := 1; Chi >= 2-*maxG; Chi-- {
		maxL := 8 - 2*Chi
		if Chi >= 0 {
			maxL = *stPeriod
		}
		for L := 1; L <= maxL; L++ {
			for chi := 1; L*chi >= Chi; chi-- {
				NOCoverings(Chi, chi, L, L*chi-Chi, func(c covering) {
					ln := c.String()
					_, key, epi := parse(ln)
					epiPlus := 0
					if Chi%2 == 0 {
						epiPlus = m[1-Chi/2][key]
					}
					if epi-epiPlus < 0 {
						panic("epi < 0; orientable surface orbifold file corrupted?")
					}
					fmt.Println(Chi, key, epi, epiPlus)
				})
			}
		}
		if Chi >= 0 {
			fmt.Printf("# .... <infinite series for Chi = %d truncated to L = %d>\n", Chi, *stPeriod)
		}
	}
}
