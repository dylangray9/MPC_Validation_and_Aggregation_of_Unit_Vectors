/*
* Copyright (c) 2016-2017,  University of California, Los Angeles
* Coded by Dylan Gray/Josh Joy
* All rights reserved.
*
* Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:
*
* Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.
* Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer
* in the documentation and/or other materials provided with the distribution.
* Neither the name of the University of California, Los Angeles nor the names of its contributors
* may be used to endorse or promote products derived from this software without specific prior written permission.
* THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO,
* THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
* FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
* SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
* WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*/

package main

import (
	crand "crypto/rand"
	"errors"
	"fmt"
	"log"
	"math"
	"math/big"
	"net"
	"net/rpc"
	"os"
	sv "share_verification"
	"sssa"
	"strconv"
	"strings"
	"time"
)

// initial stage string
// 
const BGW_STAGE_START = ""
// delimiter between stages
// 
const BGW_STAGE_DELIM = ":"

// ports used by this server
//
var PORT = sv.PortPair{Client: "0", Server: "0"}
// number of times to retry after network failure
// 
var RETRY_COUNT = 10

// structure to pass data to other aggregation servers
// 
type RPCData struct {
	Client_id, Position int
	Stage string
	Val []byte
}

/*
 * Instantiate the server and prepare it to handle RPC calls
 * Inputs:
 *     srv - this server
 */
func Start_server(srv Server) error {
	// handle server requests
	// 
	
	port := srv.Port
	PORT.Client = port.Client
	PORT.Server = port.Server
	
	// register RPC commands
	// 
	bgwrpc := new(BGWRPC)
	for retries := 0; retries < RETRY_COUNT + 1; retries ++ {
		err := rpc.Register(bgwrpc)
		
		// after retrying enough times, fail this attempt
		// 
		if err != nil && retries == RETRY_COUNT {
			fmt.Println("line 189")
			log.Println(err)
			return err
		} else if err == nil {
			break
		}
	}
	rpc.HandleHTTP()
	
	// listen for TCP connections
	// 
	l := *new(net.Listener)
	e := error(nil)
	for retries := 0; retries < RETRY_COUNT + 1; retries ++ {
		l, e = net.Listen("tcp", ":" + port.Client)
		
		// after retrying enough times, fail this attempt
		//
		if e != nil && retries == RETRY_COUNT {
			fmt.Println("line 208")
			log.Println(e)
			return e
		} else if e == nil {
			break
		}
	}
	
	// serve TCP connections
	// 
	rpc.Accept(l)
	l.Close()
	
	return nil
}

//////////////////////
// BGW Dependencies //
//////////////////////
/*
 * BGW function dependencies
 * 
 *             bits
 *     ________| | |____
 *    |          |      \
 *  solved_bits  |     bit-add
 *    |       \  |       |
 *   ran      bit-lt  carries
 *                \      |
 *                 \    pre_o
 *                  \   /
 *                  pre_or
 * 
 * note: all functions for BGW pulled from Damgard et al. The numbered comments
 * correspond to the steps in the algorithms published in "Unconditionally
 * Secure Constant-Rounds Multi-party Computation for Equality, Comparison, Bits
 * and Exponentiation".
 */
 
 
/*
 * Arguments for various BGW functions, such as multiplication
 */
type Bgw_args struct {
	A, V [][]*big.Int
	V_inv_0, X []*big.Int
	Server_list []sv.Server
	Id, Position, T int
	Fss *big.Int
}

type BGWRPC int
type RPCRes bool
 
/*
 * This computes a|b for encrypted shares
 * Inputs:
 *     a: first value to bitwise or
 *     b: second value to bitwise or
 *     args: bgw_args
 *     stage: stage id passed to identify data transfers
 * Ouputs:
 *     a|b in encrypted form
 */
func Bgw_or(a *big.Int, b *big.Int, args Bgw_args, stage string) (*big.Int, error) {
	// a V b = a + b - a*b
	// 
	tmp, err := Bgw_mult(a, b, args, get_stage_str(stage, 0, -1))
	
	if err != nil {
		return nil, err
	}
	
	return sv.Ff_sub(sv.Ff_add(a, b, args.Fss), tmp, args.Fss), nil
}

/*
 * This computes a&b for encrypted shares
 * Inputs:
 *     a: first value to bitwise and
 *     b: second value to bitwise and
 *     args: bgw_args
 *     stage: stage id passed to identify data transfers
 * Ouputs:
 *     a&b in encrypted form
 */
func Bgw_and(a *big.Int, b *big.Int, args Bgw_args, stage string) (*big.Int, error) {
	// a ^ b = a*b
	// 
	return Bgw_mult(a, b, args, get_stage_str(stage, 0, -1))
}

/*
 * This computes the prefix-or of the input.
 * Used in bgw bit-decomposition.
 * Inputs:
 *     a: Array of {0,1} values
 *     args: arguments for general BGW circuit
 *     stage: stage id passed to identify data transfers
 * Output:
 *     b: array where b[i] = OR_{j=0}^i a_j
 */
func bgw_pre_or(a []*big.Int, args Bgw_args, stage string) ([]*big.Int, error) {
	step := 0
	lambda := int(math.Ceil(math.Sqrt(float64(len(a)))))
	x := make([]*big.Int, lambda)
	y := make([]*big.Int, lambda)
	f := make([]*big.Int, lambda)
	g := make([][]*big.Int, lambda)
	c := make([]*big.Int, lambda)
	b := make([]*big.Int, int(lambda * lambda))
	s := make([][]*big.Int, lambda)
	err := error(nil)
	
	// 1. calculate x_i
	// 
	for i := 0; i < lambda; i++ {
		x[i] = big.NewInt(0)
		
		for j := 0; j < lambda && i*lambda + j < len(a); j++ {
			x[i], err = Bgw_or(x[i], a[i*lambda + j], args, get_stage_str(stage, 0, i*lambda + j))
			
			if err != nil {
				return nil, err
			}
		}
	}	
	step++
	
	// 2. calculate y_i
	//
	for i := 0; i < lambda; i++ {
		y[i] = big.NewInt(0)
		
		for k := 0; k <= i; k++ {
			y[i], err = Bgw_or(y[i], x[k], args, get_stage_str(stage, 0, i*lambda + k))
			
			if err != nil {
				return nil, err
			}
		}
	}
	step++
	
	// 3,4. set f_i
	//
	f[0] = x[0]
	for i := 1; i < lambda; i++ {
		f[i] = sv.Ff_sub(y[i], y[i-1], args.Fss)
	}
	
	// 5. set g
	// 
	for i := 0; i < lambda; i++ {
		g[i] = make([]*big.Int, lambda)
		
		for j := 0; j < lambda; j++ {
			if i*lambda + j < len(a) {
				g[i][j], err = Bgw_mult(f[i], a[i*lambda + j], args, get_stage_str(stage, 0, i*lambda + j))
			} else {
				g[i][j] = big.NewInt(0)
			}
			
			if err != nil {
				return nil, err
			}
		}
	}
	step++
	
	// 6. set c
	// 
	for j := 0; j < lambda; j++ {
		sum := big.NewInt(0)
		
		for i := 0; i < lambda; i++ {
			sum = sv.Ff_add(sum, g[i][j], args.Fss)
		}
		
		c[j] = sum
	}
	
	// 7. initialize b values
	// 
	for j := 0; j < lambda; j++ {
		b[j] = big.NewInt(0)
		
		for k := 0; k <= j; k++ {
			b[j], err = Bgw_or(b[j], c[k], args, get_stage_str(stage, 0, j*lambda + k))
			
			if err != nil {
				return nil, err
			}
		}
	}
	step++
	
	// 8. set s
	// 
	for i := 0; i < lambda; i++ {
		s[i] = make([]*big.Int, lambda)
		
		for j := 0; j < lambda; j++ {
			s[i][j], err = Bgw_mult(f[i], b[j], args, get_stage_str(stage, 0, i*lambda + j))
			
			if err != nil {
				return nil, err
			}
		}
	}
	step++
	
	// 9. calculate results
	// 
	for i := 0; i < lambda; i++ {
		for j := 0; j < lambda; j++ {
			b[i*lambda + j] = sv.Ff_sub(sv.Ff_add(s[i][j], y[i], args.Fss), f[i], args.Fss)
		}
	}
	
	return b[:len(a)], nil
}


/*
 * This computes the prefix-and of the input. If a is not a square number of
 * elements, the matrix is padded and truncated to correct size at the end.
 * Used in bgw bit-decomposition.
 * Inputs:
 *     a: Array of {0,1} values
 *     args: general arguments for bgw circuit
 *     stage: stage id passed to identify data transfers
 * Output:
 *     b: array where b[i] = AND_{j=0}^i a_j
 */
func bgw_pre_and(a []*big.Int, args Bgw_args, stage string) ([]*big.Int, error) {
	res := make([]*big.Int, len(a))
	err := error(nil)
	
	res[0] = a[0]
	for i := 1; i < len(a); i++ {
		res[i], err = Bgw_and(res[i-1], a[i], args, get_stage_str(stage, 0, i))
		
		if err != nil {
			return nil, err
		}
	}
	
	return res, nil
}

/*
 * Applies the "o" operator for all elements from o to i
 * Used in bgw bit-decomposition.
 * Inputs:
 *     a: an array of elements, each of which contains (s, p, k)
 *     args: general arguments for bgw circuit
 *     stage: stage id passed to identify data transfers
 */
func bgw_pre_op_o(a [][]*big.Int, args Bgw_args, stage string) ([][]*big.Int, error) {
	b := make([][]*big.Int, len(a))
	err := error(nil)
	
	for i := 0; i < len(a); i++ {
		b[i], err = bgw_op_o(a, i + 1, args, get_stage_str(stage, 0, i))
		
		if err != nil {
			return nil, err
		}
	}
	
	return b, nil
}

/*
 * Computes the aggregate "o" operator from 0 to l. Each element in a is
 * represented as (s, p, k).
 * Used in bgw bit-decomposition.
 * Output:
 *     a three-ple (a, b, c)
 *     l: number of bits
 *     args: general arguments for bgw circuit
 *     stage: stage id passed to identify data transfers
 */
func bgw_op_o(a [][]*big.Int, l int, args Bgw_args, stage string) ([]*big.Int, error){
	// carry set / propagate / kill algorithm
	// 
	step := 0
	res := make([]*big.Int, 3)
	err := error(nil)
	
	// constant indexes
	// 
	p := 1
	k := 2
	
	// 1. set b
	// 
	and := a[0][p];
	for i := 1; i < l; i++ {
		and, err = Bgw_and(and, a[i][p], args, get_stage_str(stage, step, i))
		
		if err != nil {
			return nil, err
		}
	}

	step++
	res[1] = and
	
	// 2. set q
	//
	p_rev := make([]*big.Int, l)
	for i := l-1; i >= 0; i-- {
		p_rev[l-i-1] = a[i][p]
	}
	
	q_rev, err := bgw_pre_and(p_rev, args, get_stage_str(stage, step, -1))
	step++
	
	// 2.5 - reverse q_rev
	//
	q := make([]*big.Int, len(q_rev))
	for i := 0; i < len(q_rev); i++ {
		q[i] = q_rev[len(q_rev) - i - 1]
	}
	
	if err != nil {
		return nil, err
	}
	
	// 3,4. set c
	// 
	
	c := make([]*big.Int, l)
	c[l-1] = a[l-1][k]
	
	// used to track when goroutines finish
	// 
	sem := make(chan error, l-1)
	
	for i := 0; i < l-1; i++ {
		go func(i int) {
			c[i], err = Bgw_and(a[i][k], q[i+1], args, get_stage_str(stage, step, i))
			
			sem <- err
		} (i)
	}
	
	// wait for goruoutines to finish
	// 
	for i := 0; i < l-1; i++ {
		err = <- sem
		if err != nil {
			return nil, err
		}
	}
	step++
	
	
	// 5. sum c
	// 
	res[2] = big.NewInt(0)
	for i := 0; i < l; i++ {
		res[2] = sv.Ff_add(res[2], c[i], args.Fss)
	}
	
	// 6. calculate a
	// 
	res[0] = sv.Ff_sub(big.NewInt(1), sv.Ff_add(res[1], res[2], args.Fss), args.Fss)
	
	return res, nil
}

/*
 * Used in bgw bit-decomposition.
 * Inputs:
 *     a, b: arrays of numbers
 *     args: general arguments for bgw circuit
 *     stage: stage id passed to identify data transfers
 * Output:
 *     array of *big.Ints
 */
func bgw_carries(a []*big.Int, b []*big.Int, args Bgw_args, stage string) ([]*big.Int, error) {
	step := 0
	l := len(b)
	err := error(nil)
	
	// 1. set s
	// 
	s := make([]*big.Int, l)
	sem := make(chan error, l)
	for i := 0; i < l; i++{
		go func(j int) {
			s[j], err = Bgw_mult(a[j], b[j], args, get_stage_str(stage, step, j))
			
			sem <- err
		} (i)
	}
	
	// wait for goruoutines to finish
	// 
	for i := 0; i < l; i++ {
		err = <- sem
		if err != nil {
			return nil, err
		}
	}
	step++
	
		
	// 2. set e
	//
	e := make([][]*big.Int, l)
	for i := 0; i < l; i++ {
		// Each element in e is e[i] = (s[i], p[i], k[i]) 
		// 
		e[i] = make([]*big.Int, 3)
		
		// set s
		// 
		e[i][0] = s[i]
		
		// set p_i = a_i + b_i - 2s_i
		// 
		e[i][1] = sv.Ff_sub(sv.Ff_add(a[i], b[i], args.Fss), sv.Ff_mul(big.NewInt(2), s[i], args.Fss), args.Fss)
		
		// set k_i = 1 - s_i - p_i
		//
		e[i][2] = sv.Ff_sub(big.NewInt(1), sv.Ff_add(s[i], e[i][1], args.Fss), args.Fss)
	}
	
	// 3. set f
	// 
	f, err := bgw_pre_op_o(e, args, get_stage_str(stage, step, -1))
	step++
	
	if err != nil {
		return nil, err
	}
	
	// 4. (skipped because it is just notation changing)
	// 5. create output c_i = f[i][s]
	// 
	c := make([]*big.Int, l)
	for i := 0; i < l; i++ {
		c[i] = f[i][0]
	}
	
	return c, nil
}

/*
 * Bitwise sum used by bgw bit-decomposition.
 * Inputs: 
 *     a: first bit-array to multiply. a[i] = {0,1}
 *     b: second bit-array to multiply
 *     args: bgw_args used to ensure correct operation
 *     stage: stage id passed to identify data transfers
 * Output:
 *     l+1 long vector which is a+b
 */
func bgw_bit_add(a []*big.Int, b []*big.Int, args Bgw_args, stage string) ([]*big.Int, error) {
	step := 0
	l := len(b)
	two := big.NewInt(2)
	
	// 1. set c
	// 
	c, err := bgw_carries(a,b, args, get_stage_str(stage, step, -1))
	step++
		
	if err != nil {
		return nil, err
	}
	
	// 2,3. set d_0 and d_l
	// 
	d := make([]*big.Int, l + 1)
	// d_0 = a_0 + b_0 - 2c_1    (c_1 is stored at c[0])
	// 
	d[0] = sv.Ff_sub(sv.Ff_add(a[0], b[0], args.Fss), sv.Ff_mul(big.NewInt(2), c[0], args.Fss), args.Fss)
	d[l] = c[l-1]
	
	// 4. set values of d_i = a_i + b_i + c_i - 2c_(i+1)
	// 
	for i := 1; i < l; i++ {
		d[i] = sv.Ff_add(sv.Ff_add(a[i], b[i], args.Fss), sv.Ff_sub(c[i-1], sv.Ff_mul(two, c[i], args.Fss), args.Fss) , args.Fss)
	}
		
	// 5. output
	// 
	return d, nil
}


/*
 * Performs a bitwise less than on encrypted shares. Returns an encrypted share
 * of 1 if a < b and 0 otherwise.
 * Inputs:
 *     a,b: values to perform a bitwise < on.
 *     args: general arguments for bgw circuit
 *     stage: stage id passed to identify data transfers
 */
func bgw_bit_lt(a []*big.Int, b []*big.Int, args Bgw_args, stage string) (*big.Int, error) {
	l := len(a)
	err := error(nil)
	step := 0
	
	// 1. set e
	// 
	e := make([]*big.Int, l)
	for i := 0; i < l; i++ {
		// this is equivalent to e[i] = xor(a[i], b[i])
		// 
		tmp := sv.Ff_sub(a[i], b[i], args.Fss)
		e[i], err = Bgw_mult(tmp, tmp, args, get_stage_str(stage, step, i))
		
		if err != nil {
			return nil, err
		}
	}
	step++
	
	
	// 2. set f
	//
	e_rev := make([]*big.Int, len(e))
	for i := 0; i < len(e); i++ {
		e_rev[i] = e[len(e) - i - 1]
	}
	
	f_rev, err := bgw_pre_or(e_rev, args, get_stage_str(stage, step, -1))
	step++
	
	if err != nil {
		return nil, err
	}
	
	// 2.5 reverse f
	//
	f := make([]*big.Int, len(f_rev))
	for i := 0; i < len(f_rev); i++ {
		f[i] = f_rev[len(f) - i - 1]
	}
	
	// 3,4. set g
	// 
	g := make([]*big.Int, l)
	g[l-1] = f[l-1]
	for i := 0; i < l-1; i++ {
		g[i] = sv.Ff_sub(f[i], f[i+1], args.Fss)
	}
	
	// 5. set h
	// 
	h := make([]*big.Int, l)
	for i := 0; i < l; i++ {
		h[i], err = Bgw_mult(g[i], b[i], args, get_stage_str(stage, step, i))
		
		if err != nil {
			return nil, err
		}
	}
	step++
	
	// 6,7. generate output
	// 
	sum := h[0]
	for i := 1; i < l; i++ {
		sum = sv.Ff_add(sum, h[i], args.Fss)
	}
	
	return sum, nil
	
}

/*
 * Generate random numbers for bgw bit-decomposition.
 * An error can be thrown, and results are invalid if this happens.
 * Inputs:
 *     args: general arguments for bgw circuit
 *     stage: stage id passed to identify data transfers
 * Output:
 *     a share of a random 0 or 1
 */
func bgw_ran2(args Bgw_args, stage string) (*big.Int, error) {
	step := 0
	err := error(nil)
	
	// 1. randomness
	// 
	a, err := bgw_ran_p(args, get_stage_str(stage, step, -1))
	if err != nil {
		return nil, err
	}
	step++
	
	// 2,3. Calculate a^2
	// 
	a_sq_p, err := Bgw_mult(a, a, args, get_stage_str(stage, step, -1))
	if err != nil {
		return nil, err
	}
	step++
	
	a_sq, err := Bgw_reveal(a_sq_p, args, get_stage_str(stage, step, -1))
	step++
	a_sq_mod_p := sv.Ff_mod(a_sq, args.Fss)
	
	if err != nil {
		return nil, err
	}
	
	
	// 4. abort if a^2 is 0
	//
	if a_sq_mod_p.Cmp(big.NewInt(0)) == 0 {
		return big.NewInt(0), errors.New("Error generating random values.")
	}
	
	// 5. set b
	// 
	b := new(big.Int).ModSqrt(a_sq_mod_p, args.Fss)
	
	// 6. set c
	//
	c := sv.Ff_mul(sv.Ff_inv(b, args.Fss), a, args.Fss)
		
	// 7,8. Generate d and output
	// 
	d := sv.Ff_mul(sv.Ff_inv(big.NewInt(2), args.Fss), sv.Ff_add(c, big.NewInt(1), args.Fss), args.Fss)
		
	return d, nil
}

/*
 * Inputs:
 *     l: number of bits
 *     args: general arguments for bgw circuit
 *     stage: stage id passed to identify data transfers
 * Outputs (b_B, b_p)
 *     b_B is a list of random bit values
 *     b_p decicmal value of b_B
 * If an error is thrown, results are invalid
 */
func bgw_solved_bits(l int, args Bgw_args, stage string) ([]*big.Int, *big.Int, error) {
	step := 0
	err := error(nil)
	p := bigInt_to_bits(args.Fss, l)
	
	// 1,2. set b_B
	//
	b_B := make([]*big.Int, l)
	sem := make(chan error, l)
	for i := 0; i < l; i++ {
		go func(i int) {
			err_local := errors.New("place-holder")
			for err_local != nil {
				b_B[i], err_local = bgw_ran2(args, get_stage_str(stage, step, i))
			}
			sem <- err_local
		} (i)
	}
	
	// wait for goruoutines to finish
	// 
	for i := 0; i < l; i++ {
		err = <- sem
		if err != nil {
			return nil, nil, err
		}
	}
	step++
	
	// 3. find bit-lt
	// 
	c, err := bgw_bit_lt(b_B, p, args, get_stage_str(stage, step, -1))
	step++
	
	if err != nil {
		return nil, nil, err
	}
	
	// 4. Reveal bit-lt
	// 
	c, err = Bgw_reveal(c, args, get_stage_str(stage, step, -1))
	step++
	
	if err != nil {
		fmt.Println("failed at step 4")
		return nil, nil, err
	}
	
	// 5. abort if invalid c
	// 
	if c.Cmp(big.NewInt(0)) == 0 {
		fmt.Println("failed at step 5")
		return nil, nil, errors.New("Error finding BGW solved bits.")
	}
	
	// 6. set sum
	// 
	sum := big.NewInt(0)
	for i := 0; i < l; i++ {
		sum = sv.Ff_add(sum, sv.Ff_mul(big.NewInt(int64(math.Pow(2, float64(i)))), b_B[i], args.Fss), args.Fss)
	}
	
	return b_B, sum, nil
}

/*
 * BGW implementation of converting a secret to its bit-decomposition.
 * Inputs:
 *     a: share of an encrypted value.
 *     l: number of bits
 *     args: general arguments for bgw circuit
 *     stage: stage id passed to identify data transfers
 * Output:
 *     An array of encrypted shares of 0s and 1s which when revealed are the
 *     bit representaiton of the revealed value of a.
 */
func Bgw_bits(a *big.Int, l int, args Bgw_args, stage string) ([]*big.Int, error) {
	step := 0
	p := bigInt_to_bits(args.Fss, l+1)
	err := error(nil)
	
	// 1,2 find solved bits
	// 
	b_B, b_p, err := bgw_solved_bits(l, args, get_stage_str(stage, step, -1))
	step++
	repeat := 0
	for err != nil {
		b_B, b_p, err = bgw_solved_bits(l, args, get_stage_str(stage, step, repeat))
		repeat++
	}
	step++
	b := b_p
	
	
	// 3,4. get a-b
	// 
	c_p := sv.Ff_sub(a, b, args.Fss)
	c, err := Bgw_reveal(c_p, args, get_stage_str(stage, step, -1))
	step++
	
	if err != nil {
		return nil, err
	}
	
	// 5. calculate d
	// 
	c_B := bigInt_to_bits(c, l)
	
	d, err := bgw_bit_add(c_B, b_B, args, get_stage_str(stage, step, -1))
	step++
	
	if err != nil {
		return nil, err
	}
	
	
	// 6. calculate q
	// 
	q, err := bgw_bit_lt(p, d, args, get_stage_str(stage, step, -1))
	step++
	
	if err != nil {
		return nil, err
	}
	
	
	// 7. f = 2^l - P. This needs to be non-ffs math, otherwise it makes no sense
	//
	f := bigInt_to_bits(new(big.Int).Sub(big.NewInt(int64(math.Pow(2, float64(l)))), args.Fss), l)
	
	
	// 8,9. set g
	// 
	g := make([]*big.Int, l)
	sem := make(chan error, l)
	for i := 0; i < l; i++ {
		func (i int) {
			g[i] = sv.Ff_mul(f[i], q, args.Fss)
			sem <- err
		} (i)
	}
	
	// wait for goruoutines to finish
	// 
	for i := 0; i < l; i++ {
		err = <- sem
		if err != nil {
			return nil, err
		}
	}

	
	// 10. set h to d + g
	// 
	h, err := bgw_bit_add(d, g, args, get_stage_str(stage, step, -1))
	step++
	
	
	if err != nil {
		return nil, err
	}
	
	// 11,12. calculate bits and return
	// 
	return h[0:l], nil
}

/*
 * Distributed, secret generation of random number.
 * Inputs:
 *     args: general arguments for bgw circuit
 *     stage: stage id passed to identify data transfers
 */
func bgw_ran_p(args Bgw_args, stage string) (*big.Int, error) {
	step := 0
	
	// pick random number
	//
	r, err := crand.Int(sv.RAND, args.Fss)

	if err != nil {
		return nil, err
	}

	// encrypt & distribute
	// 
	vals := sssa.Encode(args.T, r, args.X, args.Fss)
	recv, err := bgw_send_recv_array(vals, args, get_stage_str(stage, step, -1))
	step++
	
	if err != nil {
		return nil, err
	}
	
	// sum values
	// 
	sum := big.NewInt(0)
	for i := 0; i < len(recv); i++ {
		sum = sv.Ff_add(sum, recv[i], args.Fss)
	}
	
	return sum, nil
}

/*
 * Performs a BGW multiplication of a and b.
 * Inputs:
 *     a,b: encrypted values to multiply
 *     args: general arguments for bgw circuit
 *     stage: stage id passed to identify data transfers
 * Outputs:
 *     An encrypted share of a*b
 */
func Bgw_mult(a *big.Int, b *big.Int, args Bgw_args, stage string) (*big.Int, error) {	
	step := 0
	// share 0
	//
	v := sssa.Encode(args.T, big.NewInt(0), args.X, args.Fss)
	r, err := bgw_send_recv_array(v, args, get_stage_str(stage, step, -1))
	step++
	
	if err != nil {
		return nil, err
	}
	
	// calculate randomness to contribute
	//
	r_sum := big.NewInt(0)
	for i := 0; i < len(r); i++ {
		r_sum = sv.Ff_add(r_sum, r[i], args.Fss)
	}
	
	// calculate share
	// 
	share := sv.Ff_add(sv.Ff_mul(a, b, args.Fss), r_sum, args.Fss)
	
	// interpolate new share
	// 
	return bgw_matix_mult(share, args, get_stage_str(stage, step, -1))
}

/*
 * Returns the decrypted value of value a. All servers need to participate.
 * Inputs:
 *     a: value to decrypt
 *     args: general arguments for bgw circuit
 *     stage: stage id passed to identify data transfers
 * Output:
 *     The decrypted value of a
 */
func Bgw_reveal(a *big.Int, args Bgw_args, stage string) (*big.Int, error) {
	step := 0	

	// send our share and receive all other partys' shares
	//
	vals, err := bgw_send_recv_val(a, args, get_stage_str(stage, step, -1))
	step++
	
	if err != nil {
		fmt.Println("line 1218")
		fmt.Println(err)
		return nil, err
	}
	
	// get result by combining all shares
	// 
	res := sssa.Decode(vals, args.X, args.Fss);
	
	return res, nil
}

/*
 * Convert a *big.Int to its bit-decomposition.
 * Inputs:
 *     a: *big.Int to convert
 *     l: number of bits
 * Output:
 *     an l long array of *big.Int's with value {0,1}
 */
func bigInt_to_bits(a *big.Int, l int) []*big.Int {
	res := make([]*big.Int, l)
	tmp := a
	two := big.NewInt(2)
	
	for i := 0; i < l; i++ {
		res[i] = new(big.Int).Mod(tmp, two)
		tmp = new(big.Int).Div(tmp, two)
	}
	
	return res
}

/*
 * Calculates the matrix A = V*P*V^-1 where V is the vandermonde matrix, and P
 * is a diagonal matrix where P_ii = 1 if i < t, and P_ij = 0 otherwise.
 * Inputs
 *     x: locations which Shamir's Secret Sharing Algorithm used to encrypt shares
 *     t: number of parties needed to recreate the original value
 *     fss: finite field size
 * Output: (A, V^-1)
 */
func bgw_mult_matrix(x []*big.Int, t int, fss *big.Int) ([][]*big.Int, [][]*big.Int) {
	n := len(x)
	
	// calculate elements of V^-1 (nxn matrix called b)
	// 
	b := make([][]*big.Int, n)
	
	// set b[i][j]
	// 
	for i := 0; i < n; i++ {
		l := n - i - 1
		b[i] = make([]*big.Int, n)
		// initialize matrix
		// 
		for j := 0; j < n; j++ {
			b[i][j] = big.NewInt(0)
			
			// calculate numberator
			// 
			if i < n-1 {
				indexes := bgw_mult_init_indexes(n, i, j)
				
				// summation
				// 
				for indexes != nil {
					prod := big.NewInt(1)
					
					// product
					//
					for m := 0; m < l; m++ {
						prod = sv.Ff_mul(prod, x[indexes[m].Int64()], fss)
					}
					
					b[i][j] = sv.Ff_add(b[i][j], prod, fss)
					
					indexes = bgw_mult_inc_indexes(indexes, n, i, j)
				}
			} else {
				b[i][j] = big.NewInt(1)
			}
			
			// divide by denominator
			// 
			denom := big.NewInt(1)
			for m := 0; m < n; m++ {
				if m != j {
					denom = sv.Ff_mul(denom, sv.Ff_sub(x[j], x[m], fss), fss)
				}
			}
			
			b[i][j] = sv.Ff_mul(b[i][j], sv.Ff_inv(denom, fss), fss)
			if (n - i) % 2 == 0 {
				b[i][j] = sv.Ff_mul(b[i][j], sv.Ff_add(big.NewInt(-1), fss, fss), fss)
			}
		}
	}
	
	
	// calculate A[i][j]
	// 
	a := make([][]*big.Int, n)
	
	for i := 0; i < n; i++ {
		a[i] = make([]*big.Int, n)
		
		for j := 0; j < n; j++ {
			a[i][j] = big.NewInt(0)
			
			for k := 0; k < t; k++ {
				a[i][j]= sv.Ff_add(a[i][j], sv.Ff_mul(sv.Ff_exp(x[i], big.NewInt(int64(k)), fss), b[k][j], fss), fss)
			}
		}
	}
	
	return a, b
}

/*
 * Sets index array for calculating b[k][j]
 * Inputs:
 *     n: total number of shares / parties
 *     k,j: indexes for current location in b
 * Output:
 *     array of indexes
 */ 
func bgw_mult_init_indexes(n int, k int, j int) []*big.Int{
	l := n - k - 1
	indexes := make([]*big.Int, l)
	cur := 0
	
	// set all indexes to smallest values where index[a] < index[b] for
	// a < b, and index[a] != j forall a
	//
	for i := 0; i < l; i++ {
		if i == j {
			cur++
		}
		
		indexes[i] = big.NewInt(int64(cur))
		
		cur++
	}
	
	return indexes
}

/*
 * Increment index array for calculating b[k][j]
 * Inputs:
 *     indexes: array of indexes to be incremented
 *     n: number of shares / parties
 *     k,j: current locaiton in b matrix
 * Output:
 *     Array with index of next value to calculate
 */ 
func bgw_mult_inc_indexes(indexes []*big.Int, n int, k int, j int) []*big.Int{
	l := len(indexes)
	cur_max := n - 1
	one := big.NewInt(1)
	two := big.NewInt(2)
	
	// update from the end first
	// 
	for i := l - 1; i >= 0; i-- {
		if indexes[i].Int64() == int64(cur_max) || (indexes[i].Int64() == int64(j-1) && j == cur_max) {
			// search further back for update
			// 
			cur_max--
		} else if (int(indexes[i].Int64()) + (l - i) >= n && j < cur_max)|| (int(indexes[i].Int64()) + (l - i) >= n - 1 && j >= cur_max){
			// no space after this value to increment. Search farther back
			// 
			cur_max--
		} else {
			// update this value
			// 
			if indexes[i].Int64() == int64(j-1) {
				indexes[i] = new(big.Int).Add(indexes[i], two)
			} else {
				indexes[i] = new(big.Int).Add(indexes[i], one)
			}
			
			// update following values
			// 
			cur := indexes[i].Int64() + 1
			for m := i+1; m < l; m++ {
				if cur == int64(j) {
					cur++
				}
				
				indexes[m] = big.NewInt(cur)
				
				cur++
			}
			
			return indexes
		}
	}
	
	// can't update anymore
	//
	return nil
}

/*
 * Performs the matrix multiplication step of BGW multiply
 * Inputs:
 *     val: the share you are contributing to the matrix multiplication
 *     args: the arguments for the entire BGW protocol
 *     stage: stage id passed to identify data transfers
 * Output:
 *     Final value of bgw multiplication
 */
func bgw_matix_mult(val *big.Int, args Bgw_args, stage string) (*big.Int, error) {
	step := 0
	p := len(args.Server_list)
	
	// encode val & send to other parties
	// 
	v := sssa.Encode(args.T, val, args.X, args.Fss)
	
	vect, err := bgw_send_recv_array(v, args, get_stage_str(stage, step, -1))
	step++
	if err != nil {
		return nil, err
	}
	
	// compute shares of output values
	// 
	s := make([]*big.Int, p)
	for k := 0; k < p; k++ {
		s[k] = big.NewInt(0)
		
		for i := 0; i < p; i++ {
			s[k] = sv.Ff_add(s[k], sv.Ff_mul(args.A[k][i], vect[i], args.Fss), args.Fss)
		}
	}
	
	recon, err := bgw_send_recv_array(s, args, get_stage_str(stage, step, -1))
	step++
	if err != nil {
		return nil, err
	}
	
	// reconstruct outputs through a_0 = V^-1[0] * recon
	// 
	res := big.NewInt(0)	
	res = sssa.Decode(recon, args.X, args.Fss)
	
	return res, nil
}


/*
 * Performs a secure aggregation where each server has a value s_i to
 * aggregate. If the result is above threshold, it is released to all
 * participants. If not, 0 is returned.
 * Inputs:
 *     s: this servers secret
 *     thresh: public threshold to compare to aggregate before releaing
 *     num_bits: number of bits to use in bit-conversion
 *     args: general arguments for bgw circuit
 *     stage: stage id passed to identify data transfers
 * Output:
 *     decrypted aggregate if agg > thresh. 0 otherwise.
 */
func Bgw_aggregate(s *big.Int, thresh *big.Int, num_bits int, args Bgw_args, stage string) (*big.Int, error) {
	start_time := time.Now()

	p := len(args.Server_list)
	err := error(nil)
	step := 0
	
	// split all values into sss shares
	// 
	s_p := sssa.Encode(args.T, s, args.X, args.Fss)		
	
	// distribute shares
	// 
	s_p, err = bgw_send_recv_array(s_p, args, get_stage_str(stage, step, -1))
	step++
	if err != nil {
		return nil, err
	}
		
	// aggregate s
	// 
	agg := big.NewInt(0)
	for i := 0; i < p; i++ {
		agg = sv.Ff_add(agg, s_p[i], args.Fss)
	}	
		
	// s - threshold
	// 
	s_min_thresh := sv.Ff_sub(agg, thresh, args.Fss)
	
	
	// convert (s-thresh) to bit notation and release sign bit
	// 
	bits, err := Bgw_bits(s_min_thresh, num_bits, args, get_stage_str(stage, step, -1))
	step++
	if err != nil {
		return nil, err
	}
	
	
	// Only release if MSB = 0
	//
	b := sv.Ff_sub(big.NewInt(1), bits[len(bits) - 1], args.Fss)
	res_p, err := Bgw_mult(b, agg, args, get_stage_str(stage, step, -1))
	step++
	
	if err != nil {
		return nil, err
	}
	
	// release result
	//
	res, err := Bgw_reveal(res_p, args, get_stage_str(stage, step,-1))
	step++
	
	
	if sv.PRINT_DURATION {
		// print run-time in seconds
		fmt.Println(float64(time.Since(start_time).Nanoseconds()) / 1000000000.0)
	}
	
	return res, err
}

/*
 * A version of send_recv_array which is customized for bgw data transfer
 * Inputs:
 *     vals: values to send to other servers
 *     args: general arguments for bgw circuit
 *     stage: stage id passed to identify data transfers
 */ 
func bgw_send_recv_array(vals []*big.Int, args Bgw_args, stage string) ([]*big.Int, error) {
	// repackage server_list to not include our server
	// 
	server_list := make([]sv.Server, len(args.Server_list) - 1)
	j := 0
	for i := 0; i < len(server_list); i++ {
		if i == args.Position {
			j++
		}
		
		server_list[i] = args.Server_list[j]
		
		j++
	}
	
	// send and receive data
	//
	received, pos, err := send_recv_array_pos(vals, len(args.Server_list), server_list, stage, args.Id, args.Fss, args.Position)
	
	if err != nil {
		return received, err
	}
	
	// sort data based on position
	// 
	res := make([]*big.Int, len(args.Server_list))
	for i := 0; i < len(args.Server_list) - 1; i++ {
		res[pos[i]] = received[i]
	}
	
	res[args.Position] = vals[args.Position]
	
	return res, nil
}

/*
 * A version of send_recv_val which is customized for bgw data transfer
 * Inputs:
 *     val: value to send to all other servers
 *     args: general arguments for bgw circuit
 *     stage: stage id passed to identify data transfers
 */
func bgw_send_recv_val(val *big.Int, args Bgw_args, stage string) ([]*big.Int, error) {
	p := len(args.Server_list)
	
	vals := make([]*big.Int, p)
	for i := 0; i < p; i++ {
		// copy data to new structure
		// 
		vals[i] = new(big.Int).Add(val, big.NewInt(0))
	}
	
	return bgw_send_recv_array(vals, args, stage)
}


type RPC_BGW_ARGS struct {
	Secret, Thresh, Fss []byte
	A, V [][][]byte
	V_inv_0, X [][]byte
	Server_list []sv.Server
	Id, Position, T, Num_bits int
	Stage string
}

type BGWRes []byte

/*
 * RPC function to initiate BGW protocol. This is used for testing; however, it
 * is a good template for how to use in actual code, but instead of passing the
 * arguments through RPC, they would already be on the machine. RPC could be
 * used fo coordination, but not data passing.
 * Inputs:
 *     args: arguments for running BGW circuit
 *     res: data structure to store result
 */
func (t *BGWRPC) Rpc_bgw_aggregate(args *RPC_BGW_ARGS, res *BGWRes) error {
	// unpack secret
	//
	secret := new(big.Int)
	err := secret.UnmarshalText(args.Secret)
	
	if err != nil {
		return err
	}
	
	// unpack threshold
	// 
	thresh := new(big.Int)
	err = thresh.UnmarshalText(args.Thresh)
	
	if err != nil {
		return err
	}
		
	// unpack fss
	//
	fss := new(big.Int)
	err = fss.UnmarshalText(args.Fss)
	
	if err != nil {
		return err
	}
	
	// repackage BGW arguments
	//
	bgw_args := Bgw_args{
		A: make([][]*big.Int, len(args.A)), 
		V: make([][]*big.Int, len(args.V)),
		V_inv_0: make([]*big.Int, len(args.V_inv_0)),
		X: make([]*big.Int, len(args.X)),
		Server_list: args.Server_list,
		Id: args.Id,
		Position: args.Position,
		T: args.T,
		Fss: fss}
	
	// repackage A
	// 
	for i := 0; i < len(args.A); i++ {
		bgw_args.A[i] = make([]*big.Int, len(args.A[i]))
		
		for j := 0; j < len(args.A[i]); j++ {
			bgw_args.A[i][j] = new(big.Int)
			err = bgw_args.A[i][j].UnmarshalText(args.A[i][j])
			
			if err != nil {
				return err
			}
		}
	}
	
	// repackage V
	// 
	for i := 0; i < len(args.V); i++ {
		bgw_args.V[i] = make([]*big.Int, len(args.V[i]))
		
		for j := 0; j < len(args.V[i]); j++ {
			bgw_args.V[i][j] = new(big.Int)
			err = bgw_args.V[i][j].UnmarshalText(args.V[i][j])
			
			if err != nil {
				return err
			}
		}
	}
	
	// repackage V_inv_0
	// 
	for i := 0; i < len(args.V_inv_0); i++ {
		bgw_args.V_inv_0[i] = new(big.Int)
		err = bgw_args.V_inv_0[i].UnmarshalText(args.V_inv_0[i])
		
		if err != nil {
			return err
		}
	}
	
	// repackage X
	// 
	for i := 0; i < len(args.X); i++ {
		bgw_args.X[i] = new(big.Int)
		err = bgw_args.X[i].UnmarshalText(args.X[i])
		
		if err != nil {
			return err
		}
	}
	
	
	// start async thread to do BGW circuit
	// 
	res_int, _ := Bgw_aggregate(secret, thresh, args.Num_bits, bgw_args, args.Stage)
	
	// print result
	// 
	fmt.Print("Result: ")
	fmt.Println(res_int)
	
	return nil
}


/*
 * This tests the BGW circuit. It will disperse the secrets to the servers in
 * server_list, and they will sum and check against threshold. If it is above
 * the threshold, it will release sum + lagrange noise. Otherwise, it will
 * release the sum.
 * Inputs:
 *     secrets: 1 secret per party
 *     threshold: value to compare aggregate to before releasing
 *     server_list: list of servers to run the test on
 *     t: number of controlled parties this protocol is resilient to. Must be at most floor((P-1)/2)
 */
func Bgw_test(secrets []*big.Int, threshold int, server_list []sv.Server, t int) {
	err := error(nil)
	// It is useful to find the largest prime for a bit size to improve speed
	// 
	//fss, _ := big.NewInt(0).SetString("340282366920938463463374607431768211297", 10) // 128 bit
	//fss, _ := big.NewInt(0).SetString("18446744073709551557", 10) // 64 bit
	//fss, _ := big.NewInt(0).SetString("2147483647", 10)	// 31 bits
	//fss, _ := big.NewInt(0).SetString("4294967291", 10)	// 32 bits
	fss := big.NewInt(251)		// 8 bits
	num_bits := 8
	
	// check inputs
	// 
	if len(secrets) != len(server_list) {
		log.Fatal("Error: Number of secrets must be equal to the number of servers.")
	}
	
	// make sure t <= (n-1)/2
	// 
	if t > (len(server_list)- 1) / 2 {
		log.Fatal("Error: t may be at most (P-1)/2")
	}
	
	
	// create random ID
	// 
	id := sv.RAND.Int()
	
	
	// get X values
	// 
	x := make([]*big.Int, len(server_list))
	for i := 0; i < len(x); i++ {
		x[i] = new(big.Int).Rand(sv.RAND, sv.Ff_sub(fss, big.NewInt(1), fss))
		x[i].Add(x[i], big.NewInt(1))
	}
	
	// create A and V_inv_0 matrices
	// 
	a, v := bgw_mult_matrix(x, t, fss)
	
	// create arguments
	// 
	f, err := fss.MarshalText()
	if err != nil {
		log.Fatal("Error: Could not marshal FSS for RPC call.")
	}
	
	// marhsal threshold
	// 
	thresh, err := big.NewInt(int64(threshold)).MarshalText()
	if err != nil {
		log.Fatal("Error: Could not marshal negative threshold for RPC call.")
	}
	
	a_byte := make([][][]byte, len(a))
	for i := 0; i < len(a); i++ {
		a_byte[i] = make([][]byte, len(a[i]))
		
		for j := 0; j < len(a[i]); j++ {
			a_byte[i][j], err = a[i][j].MarshalText()
			
			if err != nil {
				log.Fatal("Error: Could not marshal A matrix for RPC call.")
			}
		}
	}
	
	v_byte := make([][][]byte, len(v))
	for i := 0; i < len(v); i++ {
		v_byte[i] = make([][]byte, len(v[i]))
		for j := 0; j < len(v[i]); j++ {
			v_byte[i][j], err = v[i][j].MarshalText()
			
			if err != nil {
				log.Fatal("Error: could not marshal V matrix for RPC call.")
			}
		}
	}
	
	v_inv_0_byte := make([][]byte, len(v[0]))
	for i := 0; i < len(v[0]); i++ {
		v_inv_0_byte[i], err = v[0][i].MarshalText()
		
		if err != nil {
			log.Fatal("Error: Could not marshal V matrix for RPC call.")
		}
	}
	
	x_byte := make([][]byte, len(x))
	for i := 0; i < len(x); i++ {
		x_byte[i], err = x[i].MarshalText()
		
		if err != nil {
			log.Fatal("Error: Could not marshal X array for RPC call.")
		}
	}
	
	arg := &RPC_BGW_ARGS{
		Secret: nil,
		Thresh: thresh,
		Fss: f,
		A: a_byte,
		V: v_byte,
		V_inv_0: v_inv_0_byte,
		X: x_byte,
		Server_list: server_list,
		Id: id,
		Position: -1,
		T: t,
		Num_bits: num_bits,
		Stage: BGW_STAGE_START}
	
	res := make([]BGWRes, len(server_list))
	client := make([]*rpc.Client, len(server_list))
	calls := make([]*rpc.Call, len(server_list))
	
	// use RPC to start BGW circuit
	// 
	for i := 0; i < len(server_list); i++ {		
		// connect to each server
		// 
		for retries := 0; retries < sv.RETRY_COUNT + 1; retries ++ {
			client[i], err = rpc.Dial("tcp", server_list[i].Address + ":" + server_list[i].Port.Client)
			
			// after retrying enough times, fail this attempt
			//
			if err != nil && retries == sv.RETRY_COUNT {
				log.Fatal("Error: Could not connect to clients.")
			} else if err == nil {
				break
			}
		}
		
		// update argument for this server. Must update:
		//     - Secret
		//     - Lagrange
		//     - Position
		// 
		arg.Secret, err = secrets[i].MarshalText()
		if err != nil {
			log.Fatal("Error marshalling secret for RPC.")
		}
				
		arg.Position = i

		
		// send request
		// 
		for retries := 0; retries < sv.RETRY_COUNT + 1; retries ++ {
			calls[i] = client[i].Go("BGWRPC.Rpc_bgw_aggregate", arg, &res[i], nil)
			
			// after retrying enough times, fail this attempt
			//
			if err != nil && retries == sv.RETRY_COUNT {
				log.Fatal("Error: Could not send RPC requests.")
			} else if err == nil {
				break
			}
		}
	}
	
	return
}


/*
 * Create string to represent the stange for data transfer.
 */
func get_stage_str (stage string, step int, itr int) string {
	if itr < 0 {
		return stage + BGW_STAGE_DELIM + strconv.Itoa(step)
	} else {
		return stage + BGW_STAGE_DELIM + strconv.Itoa(step) + BGW_STAGE_DELIM + strconv.Itoa(itr)
	}
}


////////////////////////////
// data passing functions //
////////////////////////////
/*
 * split an array of values across servers, so each gets a unique value.
 * Inputs:
 *     vals: values to send to servers (length p)
 *     p: number of parties including this one
 *     server_list: servers to send data to (length p - 1)
 *     stage: stage id passed to identify data transfers
 *     client_id: unique identifier for the client. Used so multiple
 *         simultaneous verifications can happen
 *     fss: finite field size
 * Output:
 *     an array of values received from all other servers (as well as the value
 *     we saved for ourselves)
 * Note: val[pos] is "sent" to ourselves, so we can skip it
 */
func send_recv_array(vals []*big.Int, p int, server_list []sv.Server, stage string, client_id int, fss *big.Int) ([]*big.Int, []int, error) {
	return send_recv_array_pos(vals, p, server_list, stage, client_id, fss, 0)
}
 
func send_recv_array_pos(vals []*big.Int, p int, server_list []sv.Server, stage string, client_id int, fss *big.Int, pos int) ([]*big.Int, []int, error) {
	res := make([]sv.RPCAck, p - 1)
	err :=  error(nil)
	client := make([]*rpc.Client, len(server_list))
	calls := make([]*rpc.Call, len(server_list))
	arg := RPCData{Client_id: client_id, Stage: stage, Val: nil, Position: pos}
	rpc_res := make([]*rpc.Call, len(server_list))

	j := 0
	for i := 0; i < len(server_list); i++ {
		if i == pos {
			j++
		}
		
		for retries := 0; retries < RETRY_COUNT + 1; retries++ {
			client[i], err = rpc.Dial("tcp", server_list[i].Address + ":" + server_list[i].Port.Client)
			
			// after retrying enough times, fail this attempt
			//
			if err != nil && retries == RETRY_COUNT {
				return nil, nil, err
			} else if err == nil {
				break
			}
		}
		
		
		// send data and requests
		// 
		arg.Val, err = vals[j].MarshalText()
		if err != nil {
			return nil, nil, err
		}
		
		for retries := 0; retries < RETRY_COUNT + 1; retries++ {
			calls[i] = client[i].Go("BGWRPC.Rpc_send_data", arg, &res[i], nil)
			
			// after retrying enough times, fail this attempt
			//
			if err != nil && retries == RETRY_COUNT {
				return nil, nil, err
			} else if err == nil {
				break
			}
		}
		
		j++
	}
	
	// wait for processes to end
	// 
	for i := 0; i < len(server_list); i++ {
		rpc_res[i] = <-calls[i].Done
		
		if (rpc_res[i] != calls[i]) {
			i--
			time.Sleep(10 * time.Millisecond)
		} else {
			client[i].Close()
		}
	}
	
	// check ACKs
	// 
	acks := true
	for i := 0; i < len(server_list); i++ {
		acks = acks && bool(res[i])
	}
	
	if !acks {
		log.Println("Not all ACKs were positive")
		return nil, nil, errors.New("Not all ACKS were positive")
	}
	
	// get shares from other servers
	// 
	return sv.Get_data_value(sv.RPCKey{Client_id: client_id, Stage: stage}, p)
}

/*
 * Send the same value to every server
 * Inputs:
 *     val: value to send
 *     p: number of parties including this one
 *     server_list: servers to send data to (length p - 1)
 *     stage: where in the verification process we are
 *     client_id: unique identifier for the client. Used so multiple
 *         simultaneous verifications can happen
 *     fss: finite field size
 * Output:
 *     array of values received from other servers
 */
func send_recv_val(val *big.Int, p int, server_list []sv.Server, stage string, client_id int, fss *big.Int) ([]*big.Int, error) {
	vals := make([]*big.Int, p)
	for i := 0; i < p; i++ {
		vals[i] = new(big.Int).Add(val, big.NewInt(0))
	}
	
	res, _, err := send_recv_array(vals, p, server_list, stage, client_id, fss)
	return res, err
}

/*
 * Send data over RPC. This is called by servers to send shares and sums
 * Inputs:
 *     args: RPCData which we wish to store on the server
 *     res: set to true if update succedes
 */
func (t *BGWRPC) Rpc_send_data(args *RPCData, res *sv.RPCAck) error {
	*res = false
	
	a := big.NewInt(0);
	a.UnmarshalText(args.Val)
	sv.Add_data_key_value(sv.RPCKey{Client_id: args.Client_id, Stage: args.Stage}, a, args.Position)
	
	*res = true
	return nil
}