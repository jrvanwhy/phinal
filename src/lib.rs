// This library implements a variation on the segmented Sieve of Eratosthenes
// to compute the value of Euler's totient function.

// Things to think about/change:
// How should the cur_seg vector's capacity be handled?

// Prob 243 before division-minimization modifications:
// 0m56.404s

// Prob 243 before 2^k factor optimizations:
// 0m21.145s

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
	phi_multiplier: u32, // The amount the totient is multiplied by
	div_multiplier: u32, // The amount the known divisor is multiplied by
	offset: u64,     // Component's offset relative to the current segment
	step: u64,       // Amount to bump the offset by after applying this component to a number
}

// Structure containing data for one sieve segment element
struct SegElem {
	phi: u64, // The known components of phi(x)
	div: u64, // The product of the known prime power divisors of phi(x)
}

// Structure containing information about a "future" prime power --
// a power of a prime that we have yet to reach.
struct FuturePrimePow {
	prime: u32, // The prime this is a power of
	power: u64, // The power.
}

// Iterator that spits out successive values of phi(n),
// starting at phi(0) = 0 to make the standard library's
// indexing functions work (i.e. PhiIter.new().nth(2) returns phi(2))
pub struct PhiIter {
	// Values contributing to this segment's totients
	tot_comps: Vec<TotComponent>,

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
			primes: vec![2],
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
		loop {
			if self.cur_prime_idx >= self.primes.len() as u32 {
				break
			}

			// Type cast for convenience...
			let new_prime = self.primes[self.cur_prime_idx as usize] as u64;

			// Abort if this prime is too large,
			// updating the stored current prime index.
			if new_prime * new_prime > seg_max_elem {
				break
			}

			// Generate the new totient component
			self.tot_comps.push(TotComponent {
				phi_multiplier: new_prime as u32 - 1,
				div_multiplier: new_prime as u32,
				offset: new_prime * new_prime - self.seg_offset,
				step: new_prime,
			});

			// Also generate the new future prime power struct for this prime
			self.future_pows.push(FuturePrimePow {
				prime: new_prime as u32,
				power: new_prime * new_prime,
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
					div_multiplier: elem.prime,
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
		// Initialize the segment's values to 1s.
		for elem in self.cur_seg.iter_mut() {
			elem.phi = 1;
			elem.div = 1;
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
			if seg_elem.div != cur_num {
				// cur_num is divisible by a prime that's larger than anything
				// in tot_comps

				// Check whether this is a new prime
				if seg_elem.div == 1 && cur_num < std::u32::MAX as u64 {
					// Add the prime to the primes list and compute phi(p)
					self.primes.push(cur_num as u32);

					seg_elem.phi = cur_num - 1;
				} else {
					// This isn't new, just multiply by phi(p) to finish the calculation
					// of phi for this element
					seg_elem.phi *= cur_num/seg_elem.div - 1;
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
fn sum_hundred_million() {
	assert!(PhiIter::new().take(100_000_000 + 1).fold(0, |s, x| s + x) == 3039635516365908);
}
