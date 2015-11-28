// This library implements a variation on the segmented Sieve of Eratosthenes
// to compute the value of Euler's totient function.

// Things to think about/change:
// How should the cur_seg vector's capacity be handled?

// Prob 243 before division-minimization modifications:
// 0m56.404s

// Prob 243 before 2^k factor optimizations:
// 0m21.145s

// Prob 243 after 2*k factor optimizations:
// 0m21.440s

// Prob 243 after p^-1 (mod 2^64) optimization:
// 0m17.328s

// Function to compute a multiplicative inverse mod 2^64...
// num must be odd, or this will give an invalid result.
#[allow(dead_code)]
fn mult_inv(num: u64) -> u64 {
	// Method: By Euler's theorem, a^phi(n) = 1 (mod n),
	// so a^(phi(n) - 1) = a^{-1} (mod n).
	//
	// phi(2^64) = 2^64 - 2^63 = 2^63, so
	// a^-1 == a^(2^63 - 1) (mod n).
	//
	// We use exponentiation by squaring to compute this result
	(1..62).scan(num, |pow, _| { *pow = *pow * *pow; Some(*pow) }).fold(num, |out, pow| out * pow)
}

#[test]
fn three_inv() {
	assert!(3 * mult_inv(3) == 1)
}

#[test]
fn big_inv() {
	assert!(3798713 * mult_inv(3798713) == 1)
}

// Target segment size for the segmented sieve.
const TGT_SEG_SIZE: u64 = 10_000;

// "Totient component" -- Prime powers that contribute to totients in the
// current segment. Contains the relevant multiplier as well as offsetting information.
//
// Profiling determined that it's cheaper to store the offset than to
// re-compute it for each segment, since the cost of the modulo operation
// required to compute the offset relative to a segment exceeds the time
// cost associated with the extra memory use.
struct TotComponent {
	div_multiplier: u64, // The amount the remaining divisor is multiplied by
	offset: u64,     // Component's offset relative to the current segment
	step: u64,       // Amount to bump the offset by after applying this component to a number
	phi_multiplier: u32, // The amount the totient is multiplied by
}

// Structure containing data for one sieve segment element
struct SegElem {
	phi: u64, // The known components of phi(x)
	div: u64, // The product of the unknown prime power divisors of phi(x)
}

// Structure containing information about a "future" prime power --
// a power of a prime that we have yet to reach.
struct FuturePrimePow {
	power: u64, // The power.
	inverse: u64, // Multiplicative inverse of the prime.
	prime: u32, // The prime this is a power of
}

// Current offset and power for a power of two.
// Similar to totcomponent, but specific to powers of even primes
struct TwoPowComp {
	pk: u64,
	offset: u64,
}

// Iterator that spits out successive values of phi(n),
// starting at phi(0) = 0 to make the standard library's
// indexing functions work (i.e. PhiIter.new().nth(2) returns phi(2))
pub struct PhiIter {
	// Values contributing to this segment's totients
	tot_comps: Vec<TotComponent>,

	// Powers of two that we need to handle at this stage of the sieve
	twopows: Vec<TwoPowComp>,

	// The next power of two to process (like future_pows, but for 2^k)
	next_twopow: u64,

	// Full list of known useful primes.
	primes: Vec<u32>,

	// Index of the next useful prime (the smallest prime whose square we haven't reached)
	cur_prime_idx: u32,

	// Prime powers to be processed in the future
	future_pows: Vec<FuturePrimePow>,

	// Totient values for the current segment.
	cur_seg: Vec<SegElem>,

	// Current segment's offset (i.e. cur_seg[0] == phi(seg_offset))
	seg_offset: u64,

	// Current index within the segment (for the iterator)
	cur_seg_idx: usize,
}

impl PhiIter {
	// General constructor.
	pub fn new() -> Self {
		PhiIter {
			tot_comps: Vec::new(),
			twopows: vec![TwoPowComp{pk: 2, offset: 1}],
			next_twopow: 4,
			primes: Vec::new(),
			cur_prime_idx: 0,
			future_pows: Vec::new(),
			cur_seg: vec![SegElem{phi: 0, div: 1}, SegElem{phi: 1, div: 1}, SegElem{phi: 1, div: 1}],
			seg_offset: 0,
			cur_seg_idx: 0,
		}
	}

	fn process_new_segment(&mut self) {
		// Reconfigure cur_seg to be the right size and
		// initialize it
		self.init_segment();

		// Identify new primes whose square we are passing and add them to the totient
		// components and future prime powers lists
		let seg_max_elem = self.seg_offset + self.cur_seg.len() as u64 - 1;
		while self.cur_prime_idx < self.primes.len() as u32 {
			// Type cast for convenience...
			let new_prime = self.primes[self.cur_prime_idx as usize] as u64;

			// Abort if this prime is too large,
			// updating the stored current prime index.
			if new_prime * new_prime > seg_max_elem {
				break
			}

			// Pre-compute the multiplicative inverse because it's added to both the totient
			// component and future power struct
			let prime_inv = mult_inv(new_prime);

			// Generate the new totient component
			self.tot_comps.push(TotComponent {
				phi_multiplier: new_prime as u32 - 1,
				div_multiplier: prime_inv,
				offset: new_prime * new_prime - self.seg_offset,
				step: new_prime,
			});

			// Also generate the new future prime power struct for this prime
			self.future_pows.push(FuturePrimePow {
				inverse: prime_inv,
				power: new_prime * new_prime,
				prime: new_prime as u32,
			});

			self.cur_prime_idx += 1;
		}

		// Identify any "future prime powers" that are no longer future prime powers and
		// bring them into the current totcomponent list
		for elem in self.future_pows.iter_mut() {
			while elem.power <= seg_max_elem {
				// Add this power to the totient components list
				self.tot_comps.push(TotComponent {
					phi_multiplier: elem.prime,
					div_multiplier: elem.inverse,
					offset: elem.power - self.seg_offset,
					step: elem.power,
				});

				// Update its entry in future_pows
				elem.power *= elem.prime as u64;
			}
		}

		// Last, perform the expensive part of the sieve computation
		self.sieve_segment();
	}

	// Function that performs the sieve on the given sieve segment.
	// This will update the totient components for the next segment
	fn sieve_segment(&mut self) {
		// Initialize the segment's values
		let mut cur_num = self.seg_offset;
		for elem in self.cur_seg.iter_mut() {
			elem.phi = 1;
			elem.div = cur_num;
			cur_num += 1;
		}

		// Handle the powers of two.
		// First, add new powers from this segment to the two powers list
		let max_seg_num = self.seg_offset + self.cur_seg.len() as u64 - 1;
		while self.next_twopow <= max_seg_num {
			self.twopows.push(TwoPowComp { pk: self.next_twopow, offset: self.next_twopow - self.seg_offset });
			self.next_twopow <<= 1;
		}

		// Second, iterate through the stored powers and apply them to the sieve.
		for elem in self.twopows.iter_mut() {
			while elem.offset < self.cur_seg.len() as u64 {
				let seg_elem = &mut self.cur_seg[elem.offset as usize];
				if elem.pk > 2 {
					seg_elem.phi <<= 1;
				}
				seg_elem.div >>= 1;

				elem.offset += elem.pk;
			}

			// Adjust the offset for the next sieving segment
			elem.offset -= self.cur_seg.len() as u64;
		}

		// Iterate through each totient component to perform the sieve
		for component in self.tot_comps.iter_mut() {
			while component.offset < self.cur_seg.len() as u64 {
				let seg_elem = &mut self.cur_seg[component.offset as usize];
				seg_elem.phi *= component.phi_multiplier as u64;
				seg_elem.div *= component.div_multiplier as u64;

				component.offset += component.step;
			}

			// Adjust the offset for the next sieving segment
			component.offset -= self.cur_seg.len() as u64;
		}

		// Last, find the remaining prime factors within this segment.
		// Store any newly-encountered primes.
		let mut cur_num = self.seg_offset;
		for seg_elem in self.cur_seg.iter_mut() {
			if seg_elem.div != 1 {
				// cur_num is divisible by a prime that's larger than anything
				// in tot_comps

				// Check whether this is a new prime
				if seg_elem.div == cur_num && cur_num < std::u32::MAX as u64 {
					// Add the prime to the primes list and compute phi(p)
					self.primes.push(cur_num as u32);

					seg_elem.phi = cur_num - 1;
				} else {
					// This isn't new, just multiply by phi(p) to finish the calculation
					// of phi for this element
					seg_elem.phi *= seg_elem.div - 1;
				}
			}

			cur_num += 1;
		}
	}

	fn init_segment(&mut self) {
		// Compute the length for this segment
		let max_checked = self.seg_offset + self.cur_seg.len() as u64 - 1;
		self.seg_offset += self.cur_seg.len() as u64;
		let len_cons = [ TGT_SEG_SIZE, max_checked * max_checked - self.seg_offset + 1 ];
		let new_seg_len = *len_cons.iter().min().expect("Unable to compute the new segment length") as usize;

		// Set the segment storage to have the correct length

		// First, update the capacity
		let cur_seg_cap = self.cur_seg.capacity();
		if cur_seg_cap < new_seg_len {
			self.cur_seg.reserve_exact(new_seg_len - cur_seg_cap);
		} else {
			self.cur_seg.truncate(new_seg_len);
			self.cur_seg.shrink_to_fit();
		}

		while self.cur_seg.len() < new_seg_len {
			self.cur_seg.push(SegElem{phi: 1, div: 1});
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
			// Update the segment offset, sieve the new segment, then reset our
			// current in-segment counter
			self.process_new_segment();
			self.cur_seg_idx = 0;
		}

		// Grab the already-computed totient value then increment our current value state (cur_seg_idx)
		// before returning the value.
		let out = Some(self.cur_seg[self.cur_seg_idx].phi);
		self.cur_seg_idx += 1;
		out
	}
}

#[test]
fn sum_million() {
	assert!(PhiIter::new().take(1_000_000 + 1).fold(0, |s, x| s + x) == 303963552392);
}

#[test]
#[ignore]
fn sum_hundred_million() {
	assert!(PhiIter::new().take(100_000_000 + 1).fold(0, |s, x| s + x) == 3039635516365908);
}
