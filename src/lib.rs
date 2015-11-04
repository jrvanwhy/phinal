// This library implements a variation on the segmented Sieve of Eratosthenes
// to compute the value of Euler's totient function.

// Segment size for the segmented sieve.
// Some experimentation showed that this size is approximately
// optimal for my system (i7-4700MQ).
const SEGMENT_SIZE: usize = 1 << 24;

// Structure containing all the data needed to handle a single prime number during
// the sieving process
struct PrimeData {
	// The value of the prime itself
	prime: u64,

	// The prime's square (used for power-related calculations)
	psqr: u64,

	// The offset of the current prime multiple relative to the segment start
	offset: usize,

	// The first multiple of prime in the
	// next sieving segment
	cur_mult: u64,
}

// Iterator that spits out successive values of phi(n).
// We start with phi(0) = 0 so that the standard iterator
// indexing tools work correctly (i.e. phi(n) == PhiIter::new().nth(n))
pub struct PhiIter {
	// The list of primes (and all associated data) that we've discovered so far
	primes: Vec<PrimeData>,

	// Totient values for the current segment
	cur_seg: Vec<u64>,

	// Current segment's offset (i.e. cur_seg[0] == phi(seg_offset))
	seg_offset: usize,

	// Current index within the segment (for the iterator)
	cur_seg_idx: usize,
}

impl PhiIter {
	// Function to generate a new PhiIter that starts at 0
	pub fn new() -> PhiIter {
		// Create the sieve object, preallocating all relevant values.
		let mut out = PhiIter {
			primes: Vec::new(),
			cur_seg: vec![0; SEGMENT_SIZE],
			seg_offset: 0,
			cur_seg_idx: 0,
		};

		// Sieve for the first segment
		out.sieve_segment();

		out
	}

	// This performs computes the totient function for the current sieve segment.
	fn sieve_segment(&mut self) {
		// Reset the segment's storage to all ones in preparation for sieving
		for elem in self.cur_seg.iter_mut() {
			*elem = 1;
		}

		// Iterate through all the known primes and update the sieve segment using them
		for idx in 0..self.primes.len() {
			self.sieve_prime(idx);
		}

		// The first index we should look for a prime at
		let mut firstprime_idx = 0;

		// Special handling for the first segment
		if self.seg_offset == 0 {
			self.cur_seg[0] = 0;
			firstprime_idx = 2;
		}

		// Iterate through the sieve segment to find new primes and add them to the primes array.
		// We need to sieve these primes as well in case the first multiples of these primes are
		// within the same sieving segment
		for idx in firstprime_idx..self.cur_seg.len() {
			if self.cur_seg[idx] == 1 {
				let prime = (idx + self.seg_offset) as u64;
				self.primes.push(PrimeData {
					prime: prime,
					psqr: prime * prime,
					offset: idx,
					cur_mult: prime,
				});

				let prime_idx = self.primes.len() - 1;

				self.sieve_prime(prime_idx);
			}
		}
	}

	// This performs the sieve for the given PrimeData's prime (as indexed into self.primes),
	// and updates the prime data for the next sieve segment
	fn sieve_prime(&mut self, prime_idx: usize) {
		// Grab a reference to the PrimeData object to prevent repeatedly indexing primes
		let pdata = &mut self.primes[prime_idx];

		// Iterate through all multiples in the current sieving segment
		while pdata.offset < self.cur_seg.len() {
			// Current segment element reference to avoid repeated dereferencing
			let cur_elem = &mut self.cur_seg[pdata.offset];

			// Compute the effect of this prime on the segment element's totient
			let mut pk = pdata.psqr;
			while pdata.cur_mult % pk == 0 {
				*cur_elem *= pdata.prime;
				pk *= pdata.prime;
			}

			*cur_elem *= pdata.prime - 1;

			// Increment the offset to the next multiple
			pdata.offset += pdata.prime as usize;

			// Also update the multiple value
			pdata.cur_mult += pdata.prime;

		}

		// Reset the offset for the next segment
		pdata.offset -= self.cur_seg.len();
	}
}

impl Iterator for PhiIter {
	// This library should be fast enough to blow past u32's max value really quickly
	// but slow enough to never exceed the range of a u64, so we'll force
	// the item type to be u64.
	type Item = u64;

	fn next(&mut self) -> Option<Self::Item> {
		// Check if we need to sieve another segment or whether it has already been
		// computed
		if self.cur_seg_idx >= SEGMENT_SIZE {
			// Update the segment offset, sieve the new segment, then reset our
			// current in-segment counter
			self.seg_offset += self.cur_seg.len();
			self.sieve_segment();
			self.cur_seg_idx = 0;
		}

		// Grab the already-computed totient value then increment our current value state (cur_seg_idx)
		// before returning the value.
		let out = Some(self.cur_seg[self.cur_seg_idx]);
		self.cur_seg_idx += 1;
		out
	}
}
