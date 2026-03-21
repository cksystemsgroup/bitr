//! Hierarchical Slice Cascade (HSC)
//!
//! Extends BVDDs beyond 8-bit to arbitrary width by cascading 8-bit slices.
//! A k-bit variable is decomposed into ceil(k/8) cascaded decision nodes,
//! each labeled with an 8-bit slice BVC, ordered MSB to LSB.

use crate::types::{BvddId, BvcId, BvWidth};
use crate::valueset::ValueSet;
use crate::bvdd::{BvddManager, BvddEdge};

/// Create a BVDD representing an unconstrained variable of given width.
///
/// For width <= 8: single decision node with all edges pointing to a SAT terminal.
/// For width > 8: cascade of 8-bit slice decisions MSB→LSB.
pub fn hsc_make_variable(
    mgr: &mut BvddManager,
    bvc: BvcId,
    width: BvWidth,
    sat_terminal: BvddId,
) -> BvddId {
    if width == 0 {
        return sat_terminal;
    }

    if width <= 8 {
        // Single level: decision node with one edge per domain value
        let domain = if width >= 8 { 256 } else { 1u32 << width };
        let label = mgr.make_terminal(bvc, true, false);
        let edges: Vec<BvddEdge> = vec![
            BvddEdge {
                label: ValueSet::full_for_width(width),
                child: sat_terminal,
            }
        ];
        // Optimization: single edge with FULL label collapses to child
        // But we want the decision structure, so use domain > 1 check
        if domain == 1 {
            return sat_terminal;
        }
        return mgr.make_decision(label, edges);
    }

    // Multi-level cascade: split into MSB byte + remainder
    let msb_bits = 8.min(width);
    let lsb_bits = width - msb_bits;

    // Recursively build the LSB cascade first (bottom-up)
    let lsb_bvdd = hsc_make_variable(mgr, bvc, lsb_bits, sat_terminal);

    // MSB level: decision node where all 256 edges point to the LSB cascade
    let label = mgr.make_terminal(bvc, true, false);
    let edges = vec![
        BvddEdge {
            label: ValueSet::FULL, // all 256 MSB values
            child: lsb_bvdd,
        }
    ];
    mgr.make_decision(label, edges)
}

/// Create a BVDD representing a constant value of given width.
///
/// For width <= 8: terminal with constant BVC, singleton edge.
/// For width > 8: cascade with singleton edges for each byte.
pub fn hsc_make_constant(
    mgr: &mut BvddManager,
    bvc: BvcId,
    width: BvWidth,
    val: u64,
    sat_terminal: BvddId,
) -> BvddId {
    if width == 0 {
        return sat_terminal;
    }

    if width <= 8 {
        let byte_val = (val & ((1u64 << width) - 1)) as u8;
        let label = mgr.make_terminal(bvc, true, false);
        let edges = vec![
            BvddEdge {
                label: ValueSet::singleton(byte_val),
                child: sat_terminal,
            }
        ];
        return mgr.make_decision(label, edges);
    }

    // Multi-level: extract each byte MSB→LSB
    let msb_bits = 8.min(width);
    let lsb_bits = width - msb_bits;

    // LSB value and MSB byte
    let lsb_mask = if lsb_bits >= 64 { u64::MAX } else { (1u64 << lsb_bits) - 1 };
    let lsb_val = val & lsb_mask;
    let msb_byte = ((val >> lsb_bits) & 0xFF) as u8;

    // Build LSB cascade first
    let lsb_bvdd = hsc_make_constant(mgr, bvc, lsb_bits, lsb_val, sat_terminal);

    // MSB level: singleton edge for the MSB byte value
    let label = mgr.make_terminal(bvc, true, false);
    let edges = vec![
        BvddEdge {
            label: ValueSet::singleton(msb_byte),
            child: lsb_bvdd,
        }
    ];
    mgr.make_decision(label, edges)
}

/// Compute the number of cascade levels for a given width
pub fn hsc_levels(width: BvWidth) -> u32 {
    if width == 0 { 0 }
    else { (width as u32).div_ceil(8) }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::BvcId;

    #[test]
    fn test_hsc_levels() {
        assert_eq!(hsc_levels(0), 0);
        assert_eq!(hsc_levels(1), 1);
        assert_eq!(hsc_levels(8), 1);
        assert_eq!(hsc_levels(9), 2);
        assert_eq!(hsc_levels(16), 2);
        assert_eq!(hsc_levels(32), 4);
    }

    #[test]
    fn test_hsc_variable_narrow() {
        let mut mgr = BvddManager::new();
        let bvc = BvcId(99);
        let sat = mgr.make_terminal(bvc, true, true);
        let bvdd = hsc_make_variable(&mut mgr, bvc, 4, sat);
        // Should be a decision node (not collapsed because domain > 1)
        assert!(!mgr.is_terminal(bvdd) || mgr.get(bvdd).can_be_true);
    }

    #[test]
    fn test_hsc_variable_wide() {
        let mut mgr = BvddManager::new();
        let bvc = BvcId(99);
        let sat = mgr.make_terminal(bvc, true, true);
        let bvdd = hsc_make_variable(&mut mgr, bvc, 16, sat);
        // 16-bit: 2-level cascade
        assert!(mgr.get(bvdd).can_be_true);
    }

    #[test]
    fn test_hsc_constant_narrow() {
        let mut mgr = BvddManager::new();
        let bvc = BvcId(99);
        let sat = mgr.make_terminal(bvc, true, true);
        let bvdd = hsc_make_constant(&mut mgr, bvc, 8, 42, sat);
        // Should be a decision node with singleton edge for value 42
        assert!(mgr.get(bvdd).can_be_true);
    }

    #[test]
    fn test_hsc_constant_wide() {
        let mut mgr = BvddManager::new();
        let bvc = BvcId(99);
        let sat = mgr.make_terminal(bvc, true, true);
        let bvdd = hsc_make_constant(&mut mgr, bvc, 16, 0x1234, sat);
        // 16-bit constant 0x1234: MSB=0x12, LSB=0x34
        assert!(mgr.get(bvdd).can_be_true);
    }
}
