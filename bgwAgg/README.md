This library implements a secure BGW scheme which aggregates blinded inputs
(from share verification) and only reveals the value if above a publicly known
threshold. It relies on the BGW bit conversion protocol described in
"Unconditionally Secure Constant-Rounds Multi-party Computation for Equality,
Comparison, Bits and Exponentiaiton" by Damgard et al.
For more details on how it works, please read "MPC Validation and Aggregation
of Unit Vectors", by Gray, Joy, and Gerla, Technical Report No. 170001 from
UCLA. 

Warning: this can be quite slow.

To run the verification scheme, you need at least 3 servers and 1 client. If
there are fewer than 3 servers, the protocol is not secure.

Note: this relies on a modified version of the SSSA library by Alexander
Scheel. Please use the version included in this GitHub repo for compatability
purposes.

Important Functions:
- Start_server()
	- run this function to set up a server instance. It will listen for RPC
	  calls which initiate aggregation.
- Bgw_or()
	- Takes Shamir Secret Share values (a,b) and returns a|b in encrypted form.
- Bgw_or()
	- Takes Shamir Secret Share values (a,b) and returns a&b in encrypted form.
- Bgw_bits()
	- converts a Shamir Secret Share to an array of secret shares which when
	  released is the bit representation of the decrypted input.
- Bgw_mult()
	- Takes Shamir Secret Share values (a,b) and returns a*b in encrypted form.
-  Bgw_reveal()
	- Converts Shamir Secret Shares to decrypted values.
- Bgw_aggregate()
	- Performs a secure aggregation, where it takes blinded inputs from share
	  verification and returns a decrytped aggregate if it is above the
	  publicly known threshold.
- Bgw_test()
	- call this from the client machine to perform the RPC calls necessary to
	  start the aggregation on the servers.