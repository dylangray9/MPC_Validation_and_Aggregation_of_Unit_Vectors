This library implements a secure MPC scheme which verifies if a user input is
a unit vector without any server knowing the original input. For more details
on how it works, please read "MPC Validation and Aggregation of Unit Vectors",
by Gray, Joy, and Gerla, Technical Report No. 170001 from UCLA. 

To run the verification scheme, you need at least 3 servers and 1 client. If
there are fewer than 3 servers, the protocol is not secure, because if a server
knows a, and the result of an MPC circuit is c = a+b, they can find b as well.

Improtant Functions:
- Start_server()
	- run this function to set up a server instance. It will listen for RPC
	  calls which initiate verification.
- Verify()
	- call this function on the client to initialize the verification process.
	  It will in turn perform RPC calls to the servers.
- StrToServer(s string) Server
	- converts a string to the Server object. The string should be in the
	  form ip:port1:port2
- Rand_test()
	- called by client to perform verification on a random input. This is
	  helpful for ensuring you have setup the server and client correctly.
- Unit_tests()
	- called by the client to run unit tests to ensure setup validity.