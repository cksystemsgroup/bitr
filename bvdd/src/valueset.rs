use std::fmt;
use std::ops;

/// A 256-bit bitmask representing a set of byte values [0, 255].
/// Bit i is set iff value i is in the set.
///
/// Operations map directly to solving steps:
/// - AND = propagation (intersect feasible values)
/// - OR  = resolution (merge edges to same child)
/// - NOT = complement
/// - popcount = 0 -> conflict, = 1 -> unit, = 256 -> unconstrained
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct ValueSet {
    pub bits: [u64; 4],
}

impl ValueSet {
    pub const EMPTY: ValueSet = ValueSet { bits: [0; 4] };
    pub const FULL: ValueSet = ValueSet { bits: [u64::MAX; 4] };

    /// Create a singleton set containing only value `v`.
    pub fn singleton(v: u8) -> ValueSet {
        let mut vs = ValueSet::EMPTY;
        let word = (v / 64) as usize;
        let bit = v % 64;
        vs.bits[word] = 1u64 << bit;
        vs
    }

    /// Create a set from a range [lo, hi] inclusive.
    pub fn from_range(lo: u8, hi: u8) -> ValueSet {
        let mut vs = ValueSet::EMPTY;
        for v in lo..=hi {
            vs = vs.or(ValueSet::singleton(v));
        }
        vs
    }

    /// Intersection (propagation)
    #[inline]
    pub fn and(self, other: ValueSet) -> ValueSet {
        ValueSet {
            bits: [
                self.bits[0] & other.bits[0],
                self.bits[1] & other.bits[1],
                self.bits[2] & other.bits[2],
                self.bits[3] & other.bits[3],
            ],
        }
    }

    /// Union (resolution)
    #[inline]
    pub fn or(self, other: ValueSet) -> ValueSet {
        ValueSet {
            bits: [
                self.bits[0] | other.bits[0],
                self.bits[1] | other.bits[1],
                self.bits[2] | other.bits[2],
                self.bits[3] | other.bits[3],
            ],
        }
    }

    /// Complement
    pub fn complement(self) -> ValueSet {
        !self
    }

    /// Number of values in the set
    pub fn popcount(self) -> u32 {
        self.bits.iter().map(|w| w.count_ones()).sum()
    }

    #[inline]
    pub fn is_empty(self) -> bool {
        self.bits == [0; 4]
    }

    #[inline]
    pub fn is_full(self) -> bool {
        self.bits == [u64::MAX; 4]
    }

    /// Check if value `v` is in the set
    #[inline]
    pub fn contains(self, v: u8) -> bool {
        let word = (v / 64) as usize;
        let bit = v % 64;
        (self.bits[word] >> bit) & 1 == 1
    }

    /// Check if self is a subset of other
    pub fn is_subset_of(self, other: ValueSet) -> bool {
        self.and(other) == self
    }

    /// For a width < 8, mask to only valid domain values [0, 2^width - 1]
    pub fn mask_to_width(self, width: u16) -> ValueSet {
        if width >= 8 {
            return self;
        }
        let domain_size = 1u64 << width;
        // Only the first `domain_size` bits are valid
        ValueSet {
            bits: [self.bits[0] & ((1u64 << domain_size) - 1), 0, 0, 0],
        }
    }

    /// Full set for a given width: all values [0, 2^width - 1]
    pub fn full_for_width(width: u16) -> ValueSet {
        if width >= 8 {
            return ValueSet::FULL;
        }
        let domain_size = 1u64 << width;
        ValueSet {
            bits: [(1u64 << domain_size) - 1, 0, 0, 0],
        }
    }

    /// Symmetric difference (XOR)
    pub fn xor(self, other: ValueSet) -> ValueSet {
        ValueSet {
            bits: [
                self.bits[0] ^ other.bits[0],
                self.bits[1] ^ other.bits[1],
                self.bits[2] ^ other.bits[2],
                self.bits[3] ^ other.bits[3],
            ],
        }
    }

    /// Insert a value into the set
    pub fn insert(self, v: u8) -> ValueSet {
        self.or(ValueSet::singleton(v))
    }

    /// Remove a value from the set
    pub fn remove(self, v: u8) -> ValueSet {
        self.and(ValueSet::singleton(v).complement())
    }

    /// Smallest element, or None if empty
    pub fn min_element(self) -> Option<u8> {
        for (i, &w) in self.bits.iter().enumerate() {
            if w != 0 {
                return Some((i as u8) * 64 + w.trailing_zeros() as u8);
            }
        }
        None
    }

    /// Largest element, or None if empty
    pub fn max_element(self) -> Option<u8> {
        for i in (0..4).rev() {
            if self.bits[i] != 0 {
                return Some((i as u8) * 64 + 63 - self.bits[i].leading_zeros() as u8);
            }
        }
        None
    }

    /// Create a set from a predicate: includes v where f(v) is true
    pub fn from_fn(f: impl Fn(u8) -> bool) -> ValueSet {
        let mut vs = ValueSet::EMPTY;
        for v in 0..=255u8 {
            if f(v) {
                let word = (v / 64) as usize;
                let bit = v % 64;
                vs.bits[word] |= 1u64 << bit;
            }
        }
        vs
    }

    /// Iterate over all values in the set
    pub fn iter(self) -> ValueSetIter {
        ValueSetIter { vs: self, pos: 0 }
    }
}

/// Iterator over values in a ValueSet
pub struct ValueSetIter {
    vs: ValueSet,
    pos: u16,
}

impl Iterator for ValueSetIter {
    type Item = u8;

    fn next(&mut self) -> Option<u8> {
        while self.pos < 256 {
            let v = self.pos as u8;
            self.pos += 1;
            let word = (v / 64) as usize;
            let bit = v % 64;
            if (self.vs.bits[word] >> bit) & 1 == 1 {
                return Some(v);
            }
        }
        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.vs.popcount() as usize;
        (0, Some(remaining))
    }
}

impl ops::Not for ValueSet {
    type Output = ValueSet;
    fn not(self) -> ValueSet {
        ValueSet {
            bits: [
                !self.bits[0],
                !self.bits[1],
                !self.bits[2],
                !self.bits[3],
            ],
        }
    }
}

impl fmt::Debug for ValueSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let count = self.popcount();
        if count == 0 {
            write!(f, "empty")
        } else if count == 256 {
            write!(f, "[0..255]")
        } else if count <= 8 {
            let mut vals = Vec::new();
            for i in 0..=255u8 {
                if self.contains(i) {
                    vals.push(i.to_string());
                }
            }
            write!(f, "{{{}}}", vals.join(", "))
        } else {
            write!(f, "ValueSet({})", count)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_singleton() {
        let s = ValueSet::singleton(42);
        assert!(s.contains(42));
        assert!(!s.contains(41));
        assert_eq!(s.popcount(), 1);
    }

    #[test]
    fn test_and_or_not() {
        let a = ValueSet::singleton(1).or(ValueSet::singleton(2));
        let b = ValueSet::singleton(2).or(ValueSet::singleton(3));
        let inter = a.and(b);
        assert_eq!(inter, ValueSet::singleton(2));
        let union = a.or(b);
        assert_eq!(union.popcount(), 3);
    }

    #[test]
    fn test_full_empty() {
        assert!(ValueSet::EMPTY.is_empty());
        assert!(ValueSet::FULL.is_full());
        assert_eq!(ValueSet::FULL.popcount(), 256);
        assert_eq!(ValueSet::FULL.and(ValueSet::EMPTY), ValueSet::EMPTY);
    }

    #[test]
    fn test_subset() {
        let a = ValueSet::singleton(5);
        let b = ValueSet::singleton(5).or(ValueSet::singleton(10));
        assert!(a.is_subset_of(b));
        assert!(!b.is_subset_of(a));
    }

    #[test]
    fn test_width_masking() {
        let full = ValueSet::full_for_width(2);
        assert_eq!(full.popcount(), 4); // {0, 1, 2, 3}
        assert!(full.contains(0));
        assert!(full.contains(3));
        assert!(!full.contains(4));
    }

    #[test]
    fn test_xor() {
        let a = ValueSet::singleton(1).or(ValueSet::singleton(2));
        let b = ValueSet::singleton(2).or(ValueSet::singleton(3));
        let x = a.xor(b);
        assert!(x.contains(1));
        assert!(!x.contains(2));
        assert!(x.contains(3));
        assert_eq!(x.popcount(), 2);
    }

    #[test]
    fn test_min_max_element() {
        assert_eq!(ValueSet::EMPTY.min_element(), None);
        assert_eq!(ValueSet::EMPTY.max_element(), None);
        assert_eq!(ValueSet::singleton(42).min_element(), Some(42));
        assert_eq!(ValueSet::singleton(42).max_element(), Some(42));

        let s = ValueSet::singleton(10).or(ValueSet::singleton(200));
        assert_eq!(s.min_element(), Some(10));
        assert_eq!(s.max_element(), Some(200));

        assert_eq!(ValueSet::FULL.min_element(), Some(0));
        assert_eq!(ValueSet::FULL.max_element(), Some(255));
    }

    #[test]
    fn test_insert_remove() {
        let s = ValueSet::EMPTY.insert(5).insert(10);
        assert_eq!(s.popcount(), 2);
        let s2 = s.remove(5);
        assert_eq!(s2, ValueSet::singleton(10));
    }

    #[test]
    fn test_from_fn() {
        let evens = ValueSet::from_fn(|v| v % 2 == 0);
        assert_eq!(evens.popcount(), 128);
        assert!(evens.contains(0));
        assert!(evens.contains(254));
        assert!(!evens.contains(1));
    }

    #[test]
    fn test_iter() {
        let s = ValueSet::singleton(3).or(ValueSet::singleton(7)).or(ValueSet::singleton(250));
        let vals: Vec<u8> = s.iter().collect();
        assert_eq!(vals, vec![3, 7, 250]);
    }

    #[test]
    fn test_from_range() {
        let r = ValueSet::from_range(10, 15);
        assert_eq!(r.popcount(), 6);
        let vals: Vec<u8> = r.iter().collect();
        assert_eq!(vals, vec![10, 11, 12, 13, 14, 15]);
    }
}
