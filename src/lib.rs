// This library implements a variation on the segmented Sieve of Eratosthenes
// to compute the value of Euler's totient function.

// Target segment size for the segmented sieve.
const TGT_SEG_SIZE: u64 = 1_000_000;

// Iterator that spits out successive values of phi(n),
// starting at phi(0) = 0 to make the standard library's
// indexing functions work (i.e. PhiIter.new().nth(2) returns phi(2))
pub struct PhiIter {
	// The list of primes that we've discovered so far
	primes: Vec<u32>,

	// Totient and remaining divisor values in the current segment
	cur_seg: Vec<(u64, u64)>,

	// Current segment's offset (i.e. cur_seg[0] == phi(seg_offset))
	seg_offset: u64,

	// Current index within the segment (for the iterator)
	cur_seg_idx: usize,

	// Upper bound for the sieve. The sieve computes the values
	// of phi(n) for n <= ub.
	ub: u64,

	// Square root of the sieve's upper bound.
	// Note that this value's type constraint ub
	// to be no greater than (u32::MAX)^2,
	// which is fine because (u32::MAX)^2 is intractably
	// large anyway.
	sqrt_ub: u32,
}

impl PhiIter {
	// General constructor. Sets an intractably large upper bound
	pub fn new() -> Self {
		let sqrt_ub = std::u32::MAX as u64;
		Self::with_ub(sqrt_ub * sqrt_ub)
	}

	// Constructor for when the user knows what upper bound they want
	pub fn with_ub(ub: u64) -> Self {
		PhiIter {
			primes: vec![2],
			cur_seg: vec![(0, 0), (1, 0), (1, 0)],
			seg_offset: 0,
			cur_seg_idx: 0,
			ub: ub,
			sqrt_ub: (ub as f64).sqrt() as u32,
		}
	}

	fn sieve_prime(seg_offset: u64, cur_seg: &mut Vec<(u64, u64)>, prime: u32) {
		// Widen prime since all later calculations will use u64's
		let prime = prime as u64;

		// The current power of p and that power minus 1
		let mut pk = prime;
		let mut pkm1 = 1;

		// Previous totient factor
		let mut prev_pkphi = 1;

		// The value of the last element of the segment
		let max_seg_elem = seg_offset + cur_seg.len() as u64 - 1;

		// We keep exponentiating p until it exceeds the maximum element
		while pk <= max_seg_elem {
			// Compute the prime multiple relative to the segment offset
			let mut offset = (pk - (seg_offset % pk)) % pk;

			// Current totient factor (phi(p^k))
			let cur_pkphi = pk - pkm1;

			// Iterate through all the prime power's multiples in this segment
			while offset < cur_seg.len() as u64 {
				let cur_seg_elem = &mut cur_seg[offset as usize];

				cur_seg_elem.0 = cur_seg_elem.0 * cur_pkphi / prev_pkphi;
				cur_seg_elem.1 = cur_seg_elem.1 * pkm1 / pk;

				offset += pk;
			}

			// Update to the next prime power and previous totient factor
			pkm1 = pk;
			pk *= prime;
			prev_pkphi = cur_pkphi;
		}
	}

	fn sieve_segment(&mut self) {
		// Reconfigure cur_seg to be the right size and
		// initialize it
		self.init_segment();

		// Go through each prime and process its effect on the totient values
		let max_factor_prime = ((self.seg_offset + self.cur_seg.len() as u64 - 1) as f64).sqrt() as u32;
		for p in self.primes.iter().map(|&p| p).take_while(|&p| p <= max_factor_prime) {
			Self::sieve_prime(self.seg_offset, &mut self.cur_seg, p);
		}

		// Last step: Scan through to handle the remaining (larger) prime factors
		// and identify primes.
		let mut cur_num = self.seg_offset;
		for elem in self.cur_seg.iter_mut() {
			// This detects any value with a prime factor
			// greater than max_prime (including elements
			// that are primes themselves)
			if elem.1 > 1 {
				// If we're still looking for primes, check if this is a new prime
				if self.sqrt_ub as u64 >= cur_num && elem.1 == cur_num {
					self.primes.push(cur_num as u32);
				}

				// Update phi(x) to incorporate the last prime's totient
				elem.0 *= elem.1 - 1;
			}

			cur_num += 1;
		}
	}

	fn init_segment(&mut self) {
		// Compute the length for this segment
		let max_checked = self.seg_offset + self.cur_seg.len() as u64 - 1;
		self.seg_offset += self.cur_seg.len() as u64;
		let len_cons = [ TGT_SEG_SIZE, self.ub - self.seg_offset + 1, max_checked * max_checked - self.seg_offset + 1 ];
		let new_seg_len = *len_cons.iter().min().expect("Unable to compute the new segment length") as usize;

		// Reset the segment storage to all 1's (with the required length)

		// First, update the capacity
		let cur_seg_cap = self.cur_seg.capacity();
		if cur_seg_cap < new_seg_len {
			self.cur_seg.reserve_exact(new_seg_len - cur_seg_cap);
		} else {
			self.cur_seg.truncate(new_seg_len);
			self.cur_seg.shrink_to_fit();
		}

		// Revert any already-constructed elements to their starting values
		let mut cur_num = self.seg_offset;
		for elem in self.cur_seg.iter_mut() {
			*elem = (1, cur_num);

			cur_num += 1;
		}

		// Push on new values as necessary
		while self.cur_seg.len() < new_seg_len {
			self.cur_seg.push((1, cur_num));
			cur_num += 1;
		}
	}
}

impl Iterator for PhiIter {
	// This library should be fast enough to make u32 too small
	// but definitely won't be able to break past u64::MAX.
	type Item = u64;

	// Standard iterator step function.
	// Will occasionally sieve a large block then go back
	// to quick execution...
	fn next(&mut self) -> Option<Self::Item> {
		// Check if we need to sieve another segment or whether it has already been
		// computed
		if self.cur_seg_idx >= self.cur_seg.len() {
			// Check to make sure we're not done...
			if self.seg_offset + self.cur_seg.len() as u64 > self.ub {
				return None
			}
			
			// Update the segment offset, sieve the new segment, then reset our
			// current in-segment counter
			self.sieve_segment();
			self.cur_seg_idx = 0;
		}

		// Grab the already-computed totient value then increment our current value state (cur_seg_idx)
		// before returning the value.
		let out = Some(self.cur_seg[self.cur_seg_idx].0);
		self.cur_seg_idx += 1;
		out
	}
}
