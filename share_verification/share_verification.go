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

package share_verification

import (
	crand "crypto/rand"
	"errors"
	"fmt"
	"log"
	"math/big"
	"math/rand"
	"net"
	"net/rpc"
	"strings"
	"sync"
	"time"
)
/*
	"math"
	"os"
	"strconv"
*/

/* 
 * each server needs 2 ports
 * Client: port which the client connects to. RPC commands come across this port
 * Server: port used for inter-server communication
 */
type PortPair struct {
	Client, Server string
}

// ports used by this server
// 
var PORT = PortPair{Client: "0", Server: "0"}

// number of times to retry after network failure
// 
var RETRY_COUNT = 3

// number of milisenconds total to wait for data from peers
// 
var MAX_WAIT_TIME = 5000

// values used for storing data from RPC
// 
var DataFromRPC map[RPCKey]RPCValue
var DataFromRPCMutex sync.Mutex

// bool for controlling printing of timings. True -> will print execution time
// 
const PRINT_DURATION = true

// stage values for sending data over RPC
// 
const SHARE_STAGE = "1"
const SUM_STAGE = "2"

// which algoritm to use for obscuring and validation
// 
type Algorithm int
const (
	SQUARE Algorithm = 1 + iota
	PRODUCT
	INVERSE
)

var RAND *rand.Rand 

/*
 * Initialize environment
 */ 
func Init_env() {	
	// set randomization source
	// 
	RAND = rand.New(rand.NewSource(int64(time.Now().Unix())))
}

/*
 * Convert a string to a Server object. Sting is formatted as 
 * address:clientPort:serverPort
 * Inputs:
 *     s: string to convert to Server object
 */
func StrToServer(s string) Server {
	strs := strings.Split(s, ":")
	if (len(strs) != 3) {
		log.Fatal("Incorrectly formatted addresses")
	}
	
	return Server{Address: strs[0], Port: PortPair{Client: strs[1], Server: strs[2]}}
}


/*
 * This function performs random tests of the RPC share_verification function.
 * It is called by the client instance, and it dispatches one call to verify
 * at a time. Because of how the servers handle requests, the requests are
 * performed in a single thread on the client, but parallelized by the server.
 * Inputs:
 *     n: length of input unit vector
 *     server_list: a list of Server objects identifying what servers will
 *         participate in the verification process
 *     num_tests: the total number of randomized tests to perform
 */
func Rand_test(n int, server_list []Server, num_tests int, client_server Server, alg Algorithm, bits int) {
    if PRINT_DURATION {
		fmt.Println("split,blind,rpc")
	}
	
	for i := 0; i < num_tests; i++ {
        u := gen_unit_vector(n)
		
		Verify(u, n, server_list, client_server, alg, bits, false, false)
	}
}

/*
 * Performs one unit test on the array 'val with expected result 'res'. Should
 * not be used in production. Solely for testing that honest parties return the
 * correct result.
 * Inputs:
 *     val: array to test
 *     res: expected result
 *     server_list: servers to verify on
 *     client_server: this server
 *     alg: algorithm to test with
 *     bits: length of prime used in finite field
 */
func unit_test(val []*big.Int, res bool, server_list []Server, client_server Server, alg Algorithm, bits int) {
	Verify(val, len(val), server_list, client_server, alg, bits, true, res)
}

func unit_test_all_alg(val []*big.Int, res bool, server_list []Server, client_server Server, bits int) {
	unit_test(val, res, server_list, client_server, PRODUCT, bits)
	unit_test(val, res, server_list, client_server, SQUARE, bits)
	unit_test(val, res, server_list, client_server, INVERSE, bits)	
}

/*
 * run a suite of unit tests.
 * Inputs: 
 *     server_list: list of servers to verify on
 *     client_server: this server
 */
func Unit_tests(server_list []Server, client_server Server) {
	one := big.NewInt(1)
	zero := big.NewInt(0)
	
	// unit vector should pass
	//
	unit_test_all_alg([]*big.Int{one, zero, zero}, true, server_list, client_server, 256)
	
	// two 1s should fail
	// 
	unit_test_all_alg([]*big.Int{zero, zero, one, one, zero, zero}, false, server_list, client_server, 256)
	
	// all 1s should fail
	// 
	unit_test_all_alg([]*big.Int{one, one, one, one, one, one, one, one, one}, false, server_list, client_server, 256)
	
	// elements not in {0,1} should fail
	// 
	unit_test_all_alg([]*big.Int{big.NewInt(17), big.NewInt(8), big.NewInt(12)}, false, server_list, client_server, 256)
}

func gen_unit_vector(bitsize int) (u []*big.Int) {
    u=make([]*big.Int,bitsize)
    v := RAND.Int() % bitsize

    // randomly generate input
    //
    for j := 0; j < bitsize; j++ {
        if j == v {
            u[j] = big.NewInt(1)
        } else {
            u[j] = big.NewInt(0)
        }
    }
    return
}

/*
 * Uses MPC to check if the input vector is a unit vector. This should be
 * called by the client.
 * Inputs:
 *     u: input vector (should be unit)
 *     n: length of input vector
 *     server_list: a list of Server objects identifying what servers will
 *         participate in the verification process
 *     client_server:
 *     alg: algorithm to use. Square, product, or inverse
 *     bits: length of prime to use for finite field size
 *     unit: true -> this is a unit test. Make sure it has the same result as exp_res
 *     exp_res: true -> should verify. False -> should fail. Used for unit tests
 */
func Verify(u []*big.Int, n int, server_list []Server, client_server Server, alg Algorithm, bits int, unit bool, exp_res bool) {
	start_time := time.Now()

	// find number of parties
	// 
	p := len(server_list)
	fss, _ := crand.Prime(RAND, bits)
	
	// split and blind shares
	// 
	shares := split_shares(u, n, p, fss)
	if PRINT_DURATION {
		// print execution time
		// 
		fmt.Print(float64(time.Since(start_time).Nanoseconds()) / 1000000.0)
		fmt.Print(",")
		start_time = time.Now()
	}
	
	blind := blind_shares(shares, n, p, 17, alg, fss)
	if PRINT_DURATION {
		// print execution time
		// 
		fmt.Print(float64(time.Since(start_time).Nanoseconds()) / 1000000.0)
		fmt.Print(",")
		start_time = time.Now()
	}
	
	// send requests to servers
	// 
	Start_client(blind, server_list, client_server, alg, fss, unit, exp_res)

	if PRINT_DURATION {
		// print execution time
		// 
		fmt.Println(float64(time.Since(start_time).Nanoseconds()) / 1000000.0)
	}
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
	rpctype := new(RPCType)
	for retries := 0; retries < RETRY_COUNT + 1; retries ++ {
		err := rpc.Register(rpctype)
		
		// after retrying enough times, fail this attempt
		// 
		if err != nil && retries == RETRY_COUNT {
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

/*
 * Initialize RPC calls to servers. This is called by the client
 * Inputs:
 *     blind: blinded shares (eg. u*R)
 *     server_list: a list of Server objects identifying what servers will
 *         participate in the verification process
 *     alg: algorithm to use
 *     fss: finite field
 *     unit: true -> this is a unit test. Make sure it has the same result as exp_res
 *     exp_res: true -> should verify. False -> should fail. Used for unit tests
 */
func Start_client(blind [][]*big.Int, server_list []Server, client_server Server, alg Algorithm, fss *big.Int, unit bool, exp_res bool) error {
	p := len(server_list)
	res := make([]bool, p)
	client := make([]*rpc.Client, p)
	calls := make([]*rpc.Call, p)
	client_id := RAND.Int()
			
	for i := 0; i < len(server_list); i++ {
		// connect to each server
		// 
		err :=  error(nil)
		
		for retries := 0; retries < RETRY_COUNT + 1; retries ++ {
			client[i], err = rpc.Dial("tcp", server_list[i].Address + ":" + server_list[i].Port.Client)
			
			// after retrying enough times, fail this attempt
			//
			if err != nil && retries == RETRY_COUNT {
				log.Println(err)
				return err
			} else if err == nil {
				break
			}
		}
		
		// create arguments
		// 
		f, _ := fss.MarshalText()
		tmp := &RPCArgs{Blind_share: marshal_array(blind[i]), P: p, Fss: f, Client_id: client_id, Server_list: make([]Server, p - 1), Client: client_server, Alg: alg, Unit: unit, ExpRes: exp_res}
		
		count := 0
		for j := 0; j < len(server_list); j++ {
			if j != i {
				tmp.Server_list[count] = server_list[j]
				count++
			}
		}
		
		// send request
		// 
		for retries := 0; retries < RETRY_COUNT + 1; retries ++ {
			calls[i] = client[i].Go("RPCType.Rpc_share_verification", tmp, &res[i], nil)
			
			// after retrying enough times, fail this attempt
			//
			if err != nil && retries == RETRY_COUNT {
				log.Println(err)
				return err
			} else if err == nil {
				break
			}
		}
		
	}

	results := make([]*rpc.Call, len(server_list))
	for i := 0; i < len(server_list); i++ {
		results[i] = <-calls[i].Done
		client[i].Close()
	}
	
	return nil
}

type Server struct {
	Address string
	Port PortPair
}

/*
 * Convert an array of bigInt pointers to marshalled byte arrays
 * Input:
 *     arr: array of *big.Int to convert
 * Output:
 *     an array of marshalled byte arrays
 */
func marshal_array(arr []*big.Int) [][]byte {
	res := make([][]byte, len(arr))
	
	for i := 0; i < len(arr); i++ {
		res[i],_ = arr[i].MarshalText()
	}
	
	return res
}

/*
 * Convert an array of marshalled byte arrays to *big.Int's
 * Input:
 *     arr: array of marshalled byte arrays
 * Output:
 *     an array of *big.Int's representing the byte arryas
 */
func unmarshal_array(arr [][]byte) []*big.Int {
	res := make([]*big.Int, len(arr))
	
	for i := 0; i < len(arr); i++ {
		res[i] = big.NewInt(0)
		res[i].UnmarshalText(arr[i])
	}
	
	return res
}

/* 
 * Inputs for share verification over the network
 *     Blind_share: one share which was blinded by the client
 *     P: the number of parties including this one
 *     Fss: the finite space size (ie. what to mod by)
 *     Client_id: ID number for client. This allows multiple verifications to be done at once
 *     Server_list: list of addresses for other parties. Does not include this
 *         server. Length is p-1
 *     Client: the server to send results to
 */
type RPCArgs struct {
	Blind_share [][]byte
	Fss []byte
	P, Client_id int
	Server_list []Server
	Client Server
	Alg Algorithm
	Unit, ExpRes bool
}

type RPCType int
type RPCRes bool

/*
 * This function validates blinded shares received from a user, and it is done
 * via RPC over the network
 * Inputs:
 *     args: the arguments received from the client
 *     res: not used, but needed in signature for RPC to work
 */
func (t *RPCType) Rpc_share_verification(args *RPCArgs, res *RPCRes) error {
	go rpc_share_verification_async(args)
	
	
	time.After(time.Second)
	
	
	return nil
}

/*
 * share verification designed to be a Goroutine. This is used so clients do
 * not block waiting for Rpc_share_verification to finish.
 * Inputs:
 *     args: arguments from client server
 */
func rpc_share_verification_async(args *RPCArgs) error {
	start_time := time.Now()
	sum := make([]*big.Int, args.P)
	err := error(nil)
	
	fss := big.NewInt(0)
	fss.UnmarshalText(args.Fss)
	blind_shares := unmarshal_array(args.Blind_share)
	
	
	// sum elements
	//
	for i := 0; i < args.P; i++ {
		sum[i], err = rpc_mpc_sum(blind_shares[i], args.P, fss, args.Server_list, args.Client_id)
		
		if err != nil {
			return err
		}
	}
		
	// check result is valid
	// 
	result := check_results(args, sum, fss)
	
	
	if args.Unit {
		// unit tests
		//
		if result == args.ExpRes {
			fmt.Println("Unit Tests Passed")
		} else {
			fmt.Println("FAILED")
		}
	} else {
		// normal usage
		// 
		if result {
			if PRINT_DURATION { 
				fmt.Println(float64(time.Since(start_time).Nanoseconds()) / 1000000.0)
			} else {
				fmt.Println("Success")
			}
		} else {
			fmt.Println("Failure")
		}
	}
	
	return nil
}

/*
 * Check the results of the final values calculated during share verification
 * Inputs:
 *     args: arguments to the share verification process
 *     sum: array of values calculated during share verification
 */
func check_results(args *RPCArgs, sum []*big.Int, fss *big.Int) bool {
	switch (args.Alg) {
		case SQUARE:
			return check_results_square(args, sum, fss)
		case PRODUCT:
			return check_results_product(args, sum, fss)
		case INVERSE:
			return check_results_inverse(args, sum, fss)
	}
	
	// should never reach here
	return false
}
 
/*
 * check results when using the square algorithm. This checks if
 * (a + b)^2 - (a^2 + b^2) = 0
 * Inputs:
 *     args: arguments passed to verification function from client
 *     sum: array of values calculated during share verification
 */
func check_results_square(args *RPCArgs, sum []*big.Int, fss *big.Int) bool {
	for power := 2; power < args.P; power++ {
		res := Ff_exp(sum[0], big.NewInt(int64(power)), fss)
		res = Ff_sub(res, sum[power - 1], fss)
		
		if res.Int64() != 0 {
			return false
		}
	}
	
	return true
}

/*
 * check results when using the product algorithm. This checks if
 * sum[0] * sum[1] * ... * sum[p-2] - sum[p-1] = 0
 * Inputs:
 *     args: arguments passed to verification function from client
 *     sum: array of values calculated during share verification
 */
func check_results_product(args *RPCArgs, sum []*big.Int, fss *big.Int) bool {
	prod := big.NewInt(1)
	
	for i := 0; i < args.P - 1; i++ {
		prod = Ff_mul(prod, sum[i], fss)
	}
	
	res := Ff_sub(prod, sum[args.P - 1], fss)
	return res.Int64() == 0
}

/*
 * check results when using the inverse algorithm. This checks if
 * sum[0] * ... * sum[p-1] - 1 = 0
 * Inputs:
 *     args: arguments passed to verification function from client
 *     sum: array of values calculated during share verification
 */
func check_results_inverse(args *RPCArgs, sum []*big.Int, fss *big.Int) bool {
	prod := big.NewInt(1)
	
	for i := 0; i < args.P; i++ {
		prod = Ff_mul(prod, sum[i], fss)
	}
	
	res := Ff_sub(prod, big.NewInt(1), fss)
	
	return res.Int64() == 0
}

type RPCData struct {
	Client_id, Position int
	Stage string
	Val []byte
}

type RPCKey struct {
	Client_id int
	Stage string
}

type RPCValue struct {
	M *sync.Mutex
	Vals []*big.Int
	Positions []int
}

type RPCAck bool

/*
 * Send data over RPC. This is called by servers to send shares and sums
 * Inputs:
 *     args: RPCData which we wish to store on the server
 *     res: set to true if update succedes
 */
func (t *RPCType) Rpc_send_data(args *RPCData, res *RPCAck) error {
	*res = false
	
	a := big.NewInt(0);
	a.UnmarshalText(args.Val)
	Add_data_key_value(RPCKey{Client_id: args.Client_id, Stage: args.Stage}, a, args.Position)
	
	*res = true
	return nil
}

/*
 * returns p-1 values from other servers which are stored for the RPCKey value
 * Inputs:
 *     key: RPCKey which identifies the client and stage corresponding to the
 *         data we want.
 *     p: number of parties in the verification process
 * Return:
 *     an array of values of length p-1
 */
func Get_data_value(key RPCKey, p int) ([]*big.Int, []int, error) {
	wait_time := 100

	for i := 0; i * wait_time < MAX_WAIT_TIME; i++ {
		DataFromRPCMutex.Lock()
		val, exists := DataFromRPC[key]
		DataFromRPCMutex.Unlock()
		
		if exists && len(val.Vals) >= (p-1) {
			res := val.Vals
			res_pos := val.Positions
			
			DataFromRPCMutex.Lock()
			delete (DataFromRPC, key)
			DataFromRPCMutex.Unlock()
						
			return res[:(p-1)], res_pos[:(p-1)], nil
		}
		
		time.Sleep(time.Duration(wait_time) * time.Millisecond)
	}
	
	log.Println("Error: Failed to receive data from peers")
	
	return nil, nil, errors.New("Failed to receive data from peers")
}

/*
 * add a value to our data storage mapped to an RPCKey
 * Inputs:
 *     key: the RPCKey our data corresponds to
 *     val: the data to associate with the key
 */
func Add_data_key_value(key RPCKey, val *big.Int, position int) {
	DataFromRPCMutex.Lock()
	
	if (DataFromRPC == nil) {
		DataFromRPC = make(map[RPCKey]RPCValue)
	}
	
	rpc_val, exists := DataFromRPC[key]
	
	if !exists {
		// grab overall lock and create new key, value pair
		//
		DataFromRPC[key] = RPCValue{M: &sync.Mutex{}, Vals: make([]*big.Int, 1), Positions: make([]int, 1)}
		DataFromRPC[key].Vals[0] = val
		DataFromRPC[key].Positions[0] = position
		DataFromRPCMutex.Unlock()
	} else {
		// grab lock for key, value tuple and add data
		// 
		DataFromRPC[key] = RPCValue{M: rpc_val.M, Vals: append(rpc_val.Vals, val), Positions: append(rpc_val.Positions, position)}
		DataFromRPCMutex.Unlock()
	}
}

/*
 * This function takes shares and blinds them based on the random matrix. The result is
 * p vectors, each with p elements
 * Inputs:
 *     shares: p vectors each of length n. When used correctly, these should sum to a unit vector
 *     n: the length of the share vectors
 *     p: the number of parties
 *     seed: the seed for the random matrix
 *     alg: the algorithm to use for this verification
 */
func blind_shares(shares [][]*big.Int, n int, p int, seed int, alg Algorithm, fss *big.Int) ([][]*big.Int) {
	res := make([][]*big.Int, p)	// results in p vectors of length px1
	rand_matrix := gen_rand_matrix(n, p, seed, alg, fss)
	
	for i := 0; i < p; i++ {
		res[i] = make([]*big.Int, p)
	}
	
	for share_num := 0; share_num < p; share_num++ {
		// blind individual share
		// 
		
		// for each row in rand matrix
		// 
		for row := 0; row < p; row++ {
			// multiply each element in the rand matrix by the value in the share
			//
			res[share_num][row] = big.NewInt(0)
			
			for j := 0; j < n; j++ {
				res[share_num][row] = new(big.Int).Add(res[share_num][row], new(big.Int).Mul(rand_matrix[row][j], shares[share_num][j]))
			}
			
			res[share_num][row] = new(big.Int).Mod(res[share_num][row], fss)
		}
	}
	
	return res
}

/*
 * This function takes a seed and generates a PxN matrix where the first row is random, and
 * all other entries r[i][j] = r[i]^(j + 1)
 * Inputs:
 *     n: the width of the matrix
 *     p: the number of parties
 *     seed: input for RNG
 */
func gen_rand_matrix(n int, p int, seed int, alg Algorithm, fss *big.Int) ([][]*big.Int) {
	switch (alg) {
		case SQUARE:
			return gen_rand_matrix_square(n, p, seed, fss)
		case PRODUCT:
			return gen_rand_matrix_product(n, p, seed, fss)
		case INVERSE:
			return gen_rand_matrix_inverse(n, p, seed, fss)
	}
	
	// should never reach here
	return nil
}

func gen_rand_matrix_square(n int, p int, seed int, fss *big.Int) ([][]*big.Int) {
	res := make([][]*big.Int, p)
	for i := 0; i < p; i++ {
		res[i] = make([]*big.Int, n)
	}
	
	// generate top row
	// 
	for j := 0; j < n; j++ {
		r := big.NewInt(int64(RAND.Int()))
		res[0][j] = new(big.Int).Mod(r, fss)
	}
	
	// generate Ri,j = R0,j ^ (i + 1)
	// 
	for i := 1; i < p; i++ {
		for j:= 0; j < n; j++ {
			res[i][j] = Ff_exp(res[0][j], big.NewInt(int64(i + 1)), fss)
		}
	}
	
	return res
}

func gen_rand_matrix_product(n int, p int, seed int, fss *big.Int) ([][]*big.Int) {
	res := make([][]*big.Int, p)
	for i := 0; i < p; i++ {
		res[i] = make([]*big.Int, n)
	}
	
	// generate top p-1 rows
	// 
	for i := 0; i < p-1; i++ {
		for j := 0; j < n; j++ {
			r := big.NewInt(int64(RAND.Int()))
			res[i][j] = new(big.Int).Mod(r, fss)
		}
	}
	
	// generate Rp-1,j = R0,j * R1,j * ... * Rp-2,j
	// 
	for j:= 0; j < n; j++ {
		prod := big.NewInt(1)
		
		for i := 0; i < p-1; i++ {
			prod = Ff_mul(prod, res[i][j], fss)
		}
	
		res[p-1][j] = prod
	}
	
	return res
}

func gen_rand_matrix_inverse(n int, p int, seed int, fss *big.Int) ([][]*big.Int) {
	res := make([][]*big.Int, p)
	for i := 0; i < p; i++ {
		res[i] = make([]*big.Int, n)
	}
	
	// generate top p-1 rows
	// 
	for i := 0; i < p-1; i++ {
		for j := 0; j < n; j++ {
			r := big.NewInt(RAND.Int63())
			res[i][j] = new(big.Int).Mod(r, new(big.Int).Sub(fss, big.NewInt(1)))
			res[i][j] = new(big.Int).Add(big.NewInt(1), res[i][j])
		}
	}
	
	// generate Rp-1,j = R0,j * R1,j * ... * Rp-2,j
	// 
	for j:= 0; j < n; j++ {
		prod := big.NewInt(1)
		
		for i := 0; i < p-1; i++ {
			prod = Ff_mul(prod, res[i][j], fss)
		}
	
		// multiplicative inverse of the product of previous values
		// 
		res[p-1][j] = Ff_inv(prod, fss)
		
		// sometimes, a multiplicative inverse cannot be found, so retry
		if (Ff_mul(prod, res[p-1][j], fss).Int64() != 1) {
			j--
		}
	}
	
	return res
}

/*
 * This creates p vectors of length n that sum to the input vector unit
 * Inputs:
 *     u: initial vector. Should be a unit vector
 *     n: the length of the vector u
 *     p: the number of parties
 */
func split_shares(u []*big.Int, n int, p int, fss *big.Int) ([][]*big.Int) {
	res := make([][]*big.Int, p)
	
	for i := 0; i < p; i++ {
		res[i] = make([]*big.Int, n)
	}
	
	
	// for each element in u
	// 
	for i := 0; i < n; i++ {
		sum := big.NewInt(0)
		
		// for each share, generate random values
		// 
		for j := 0; j < p - 1; j++ {
			r := big.NewInt(RAND.Int63())
			tmp := new(big.Int).Mod(r, new(big.Int).Sub(fss, big.NewInt(1)))
			res[j][i] = new(big.Int).Add(tmp, big.NewInt(1))
			sum = new(big.Int).Add(res[j][i], sum)
		}
		
		// last element is in range [0, FSS-1], and causes the sum of the
		// i row of all shares to sum to the ith element of the input vector u
		// 
		res[p-1][i] = Ff_sub(u[i], sum, fss)
		
		// prevent 0's in shares
		//
		if res[p-1][i].Int64() == 0 {
			i--
		}
	}
	
	return res
}


/*
 * This function performs a sum with n parties while each party never learns
 * the value held by another party. This is done by:
 *     1. each party splits their value (x) so x = x_1 + x_2 + ... + x_p
 *     2. These shares are sent to other parties so each party gets 1 share
 *        from each party. Everyone keeps their x_1 value
 *     3. Each party sums the shares they received with their x_1. This value
 *        is the share_sum
 *     4. The share_sum values are then sent to every party, so each party has
 *        every other share_party's share_sum value
 *     5. Each party locally computes the sum of the share_sum. This the sum
 *        of all parties' initial x.
 * Inputs:
 *     val: the value from this party to sum with other parties
 *     p: number of parties, including this one
 *     fss: the finite space size
 *     server_list: addresses of parties involved, not including this server.
 *         length is p-1
 *     client_id: unique identifier for the client. Used so multiple
 *         simultaneous verifications can happen
 * Output:
 *     The sum of 'val' from all parties.
 */
func rpc_mpc_sum(val *big.Int, p int, fss *big.Int, server_list []Server, client_id int) (*big.Int, error) {	
	// split value into shares
	// 
	val_split := split_val(val, p, fss)
		
	// send val_split
	// 
	shares, _, err := send_recv_array(val_split, p, server_list, SHARE_STAGE, client_id, fss)
	
	if err != nil {
		return big.NewInt(0), err
	}
	
	share_sum := val_split[0];

	for i := 0; i < p - 1; i++ {
		share_sum = Ff_add(share_sum, shares[i], fss)
	}
	
	
	// send share_sum to others
	// 
	sums, err := send_recv_val(share_sum, p, server_list, SUM_STAGE, client_id, fss)
	
	if err != nil {
		return big.NewInt(0), err
	}

	// sum every party's shares
	// 
	sum := share_sum
	for i := 0; i < p - 1; i ++ {
		sum = Ff_add(sum, sums[i], fss)
	}
	
	return sum, nil
}

/*
 * split an array of values across servers, so each gets a unique value.
 * Inputs:
 *     vals: values to send to servers (length p)
 *     p: number of parties including this one
 *     server_list: servers to send data to (length p - 1)
 *     client_id: unique identifier for the client. Used so multiple
 *         simultaneous verifications can happen
 * Note: val[0] is "sent" to ourselves, so we can skip it
 */
func send_recv_array(vals []*big.Int, p int, server_list []Server, stage string, client_id int, fss *big.Int) ([]*big.Int, []int, error) {
	return send_recv_array_pos(vals, p, server_list, stage, client_id, fss, 0)
}
 
func send_recv_array_pos(vals []*big.Int, p int, server_list []Server, stage string, client_id int, fss *big.Int, pos int) ([]*big.Int, []int, error) {
	res := make([]RPCAck, p - 1)
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
				log.Println(err)
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
			calls[i] = client[i].Go("RPCType.Rpc_send_data", arg, &res[i], nil)
			
			// after retrying enough times, fail this attempt
			//
			if err != nil && retries == RETRY_COUNT {
				log.Println(err)
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
	return Get_data_value(RPCKey{Client_id: client_id, Stage: stage}, p)
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
 */
func send_recv_val(val *big.Int, p int, server_list []Server, stage string, client_id int, fss *big.Int) ([]*big.Int, error) {
	vals := make([]*big.Int, p)
	for i := 0; i < p; i++ {
		vals[i] = new(big.Int).Add(val, big.NewInt(0))
	}
	
	res, _, err := send_recv_array(vals, p, server_list, stage, client_id, fss)
	return res, err
}

/*
 * Splits a value into p shares. This is used to do an MPC sum of an element
 * after blinding
 * Inputs:
 *     val: value to be split_shares
 *     p: number of parties to split amongst
 * Output:
 *     returns an int array of length p whose elements sums to val
 */
func split_val(val *big.Int, p int, fss *big.Int) ([]*big.Int) {
	res := make([]*big.Int, p)
	sum := big.NewInt(0)
	
	// randomly generate first p-1 vals
	// 
	for i := 0; i < p-1; i++ {
		r := big.NewInt(int64(RAND.Int()))
		res[i] = new(big.Int).Mod(r, fss)
		//sum = (sum + res[i]) % FSS
		sum = Ff_add(sum, res[i], fss)
	}
	
	// set final value so the sum of all elements is val
	// 
	res[p-1] = Ff_sub(val, sum, fss)
	
	return res
}


/////////////////////////////
// Finite Field Operations //
/////////////////////////////

/*
 * Finite field addition: a = (a + b) % size
 * Inputs:
 *     a: first value in addition
 *     b: second value in addition
 *     size: finite field size

 */
func Ff_add(a *big.Int, b *big.Int, size *big.Int) *big.Int {
	res := new(big.Int).Add(a, b)
	res = new(big.Int).Mod(res, size)
	
	if res.Cmp(big.NewInt(0)) < 0 {
		res = new(big.Int).Add(res, size)
		res = new(big.Int).Mod(res, size)
	}
	
	return res
}

/*
 * Finite field addition: (a - b) % size
 * Inputs:
 *     a: value to subtract from
 *     b: value to subtract
 *     size: finite field size
 * Output:
 *     an int in range [0, size)
 */
func Ff_sub(a *big.Int, b *big.Int, size *big.Int) *big.Int {
	res := new(big.Int).Sub(a, b)
	res = new(big.Int).Mod(res, size)
	
	// prevent negative numbers
	// 
	if res.Cmp(big.NewInt(0)) < 0 {
		res = new(big.Int).Add(res, size)
		res = new(big.Int).Mod(res, size)
	}
	
	return res
}


/*
 * Finite field multiplication: (a * b) % size
 * Inputs:
 *     a: first value in multiplication
 *     b: second value in multiplication
 *     size: finite field size
 * Output:
 *     an int in range [0, size)
 */
func Ff_mul(a *big.Int, b *big.Int, size *big.Int) *big.Int {
	res := new(big.Int).Mul(a, b)
	res = new(big.Int).Mod(res, size)
	
	// prevent negative numbers
	// 
	if res.Cmp(big.NewInt(0)) < 0 {
		res = new(big.Int).Add(res, size)
		res = new(big.Int).Mod(res, size)
	}
	
	return res
}

/*
 * Finite field exponentiation: (a ^ b) % size
 * Inputs:
 *     a: base
 *     b: exponent
 *     size: finite field size
 * Output:
 *     an int in range [0, size)
 */
func Ff_exp(a *big.Int, b *big.Int, size *big.Int) *big.Int {
	return new(big.Int).Exp(a, b, size)
}

/*
 * Finite field inverse: (a * return) % size = 1 
 * Inputs:
 *     a: value to invert
 *     size: finite field size
 * Output:
 *     an int in range [0, size)
 */
func Ff_inv(a *big.Int, size *big.Int) *big.Int {
	return Ff_exp(a, (new(big.Int).Sub(size, big.NewInt(2))), size)
}

/*
 * Mod function for big.Int
 * Inputs:
 *     a: number to mod
 *     fss: Finite Field Size
 * Output:
 *     a % fss
 */
func Ff_mod(a *big.Int, fss *big.Int) *big.Int {
	b :=  new(big.Int).Mod(a, fss)
	
	// ensure result is positive
	// 
	if b.Cmp(big.NewInt(0)) == -1 {
		return new(big.Int).Add(b, fss)
	} else {
		return b
	}
}
