package sssa

import (
	"math/big"
)

/**
 * Returns a new arary of secret shares (encoding x,y pairs as base64 strings)
 * created by Shamir's Secret Sharing Algorithm requring a minimum number of
 * share to recreate, of length shares, from the input secret raw as a string
**/
//func Create(minimum int, shares int, raw string) []string {
func Create(minimum int, shares int, sec *big.Int, x []*big.Int, p *big.Int) [][][]*big.Int {
	// Verify minimum isn't greater than shares; there is no way to recreate
	// the original polynomial in our current setup, therefore it doesn't make
	// sense to generate fewer shares than are needed to reconstruct the secret.
	// [TODO]: proper error handling
	if minimum > shares {
		return nil
	}

	// Convert the secret to its respective 256-bit big.Int representation
	var secret []*big.Int = make([]*big.Int, 1)
	secret[0] = sec
	
	// Set constant prime across the package
	prime = p
	
	// List of currently used numbers in the polynomial
	var numbers []*big.Int = make([]*big.Int, 0)
	numbers = append(numbers, big.NewInt(0))

	// Create the polynomial of degree (minimum - 1); that is, the highest
	// order term is (minimum-1), though as there is a constant term with
	// order 0, there are (minimum) number of coefficients.
	//
	// However, the polynomial object is a 2d array, because we are constructing
	// a different polynomial for each part of the secret
	// polynomial[parts][minimum]
	var polynomial [][]*big.Int = make([][]*big.Int, len(secret))
	for i := range polynomial {
		polynomial[i] = make([]*big.Int, minimum)
		polynomial[i][0] = secret[i]

		for j := range polynomial[i][1:] {
			// Each coefficient should be unique
			number := random()
			for inNumbers(numbers, number) {
				number = random()
			}
			numbers = append(numbers, number)

			polynomial[i][j+1] = number
		}
	}

	// Create the secrets object; this holds the (x, y) points of each share.
	// Again, because secret is an array, each share could have multiple parts
	// over which we are computing Shamir's Algorithm. The last dimension is
	// always two, as it is storing an x, y pair of points.
	//
	// Note: this array is technically unnecessary due to creating result
	// in the inner loop. Can disappear later if desired. [TODO]
	//
	// secrets[shares][parts][2]
	var secrets [][][]*big.Int = make([][][]*big.Int, shares)
	var result []string = make([]string, shares)

	// For every share...
	for i := range secrets {
		secrets[i] = make([][]*big.Int, len(secret))
		// ...and every part of the secret...
		for j := range secrets[i] {
			secrets[i][j] = make([]*big.Int, 2)

			// ...and evaluate the polynomial at that point...
			secrets[i][j][0] = x[i]
			secrets[i][j][1] = evaluatePolynomial(polynomial[j], x[i])

			// ...add it to results...
			result[i] += toBase64(secrets[i][j][0])
			result[i] += toBase64(secrets[i][j][1])
		}
	}

	// ...and return!
	//return result
	return secrets
}

/**
 * Takes a string array of shares encoded in base64 created via Shamir's
 * Algorithm; each string must be of equal length of a multiple of 88 characters
 * as a single 88 character share is a pair of 256-bit numbers (x, y).
 *
 * Note: the polynomial will converge if the specified minimum number of shares
 *       or more are passed to this function. Passing thus does not affect it
 *       Passing fewer however, simply means that the returned secret is wrong.
**/
//func Combine(shares []string) string {
func Combine(shares [][][]*big.Int, p *big.Int) []*big.Int {
	// Recreate the original object of x, y points, based upon number of shares
	// and size of each share (number of parts in the secret).
	var secrets = shares
	
	// Set constant prime
	prime := p
	
	// Use Lagrange Polynomial Interpolation (LPI) to reconstruct the secret.
	// For each part of the secert (clearest to iterate over)...
	var secret []*big.Int = make([]*big.Int, len(secrets[0]))
	for j := range secret {
		secret[j] = big.NewInt(0)
		// ...and every share...
		for i := range secrets { // LPI sum loop
			// ...remember the current x and y values...
			origin := secrets[i][j][0]
			originy := secrets[i][j][1]
			numerator := big.NewInt(1)   // LPI numerator
			denominator := big.NewInt(1) // LPI denominator
			// ...and for every other point...
			for k := range secrets { // LPI product loop
				if k != i {
					// ...combine them via half products...
					current := secrets[k][j][0]
					negative := big.NewInt(0)
					negative = negative.Mul(current, big.NewInt(-1))
					added := big.NewInt(0)
					added = added.Sub(origin, current)

					numerator = numerator.Mul(numerator, negative)
					numerator = numerator.Mod(numerator, prime)

					denominator = denominator.Mul(denominator, added)
					denominator = denominator.Mod(denominator, prime)
				}
			}

			// LPI product
			// ...multiply together the points (y)(numerator)(denominator)^-1...
			working := big.NewInt(0).Set(originy)
			working = working.Mul(working, numerator)
			working = working.Mul(working, modInverse(denominator))

			// LPI sum
			secret[j] = secret[j].Add(secret[j], working)
			secret[j] = secret[j].Mod(secret[j], prime)
		}
	}

	// ...and return the result!
	//return string(mergeIntToByte(secret))
	return secret
}

/**
 * Takes in a given string to check if it is a valid secret
 *
 * Requirements:
 * 	Length multiple of 88
 *	Can decode each 44 character block as base64
 *
 * Returns only success/failure (bool)
**/
func IsValidShare(candidate string, p *big.Int) bool {
	// Set constant prime across the package
	prime := p
	
	if len(candidate)%88 != 0 {
		return false
	}

	count := len(candidate) / 44
	for j := 0; j < count; j++ {
		part := candidate[j*44 : (j+1)*44]
		decode := fromBase64(part)
		if decode.Cmp(big.NewInt(0)) == -1 || decode.Cmp(prime) == 1 {
			return false
		}
	}

	return true
}


/**
 * Creates a Shamir Secret Sharing encoding of the input value "a", evaluated
 * at the specified locations x
**/
func Encode(min int, secret *big.Int, x []*big.Int, prime *big.Int) []*big.Int {
	// encode values
	// 
	vals := Create(min, len(x), secret, x, prime)
	
	// reformat
	// 
	res := make([]*big.Int, len(x))
	for i := 0; i < len(x); i++ {
		res[i] = vals[i][0][1]
	}
	
	return res
}

/**
 * Decodes values which are shares of a SSS encoding using locations x.
**/
func Decode(shares []*big.Int, x []*big.Int, prime *big.Int) *big.Int {
	p := len(x)
	
	// format data
	// 
	vals := make([][][]*big.Int, p)
	
	for i := 0; i < p; i++ {
		vals[i] = make([][]*big.Int, 1)
		vals[i][0] = make([]*big.Int, 2)
		vals[i][0][0] = x[i]
		vals[i][0][1] = shares[i]
	}
	
	// decode
	// 
	res := Combine(vals, prime)
	
	// format answer
	// 
	return res[0]
}