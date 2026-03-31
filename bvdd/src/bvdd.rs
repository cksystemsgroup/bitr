use std::collections::HashMap;
use crate::types::{BvddId, BvcId, Canonicity};
use crate::valueset::ValueSet;

/// An edge in a BVDD decision node
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct BvddEdge {
    pub label: ValueSet,
    pub child: BvddId,
}

/// A BVDD node: either terminal (holds BVC) or decision (edges + label)
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum BvddNodeKind {
    Terminal {
        bvc: BvcId,
    },
    Decision {
        /// Label BVDD (the variable being decided on)
        label: BvddId,
        edges: Vec<BvddEdge>,
    },
}

#[derive(Debug, Clone)]
pub struct BvddNode {
    pub id: BvddId,
    pub kind: BvddNodeKind,
    /// O(1) flag: can any reachable terminal evaluate to 1?
    pub can_be_true: bool,
    /// O(1) flag: are all terminals variable-free?
    pub is_ground: bool,
    pub canonicity: Canonicity,
}

/// Key for unique table lookup
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct UniqueKey {
    kind: BvddNodeKind,
    can_be_true: bool,
    is_ground: bool,
}

/// BVDD manager: arena + unique table + computed cache
pub struct BvddManager {
    nodes: Vec<BvddNode>,
    /// Unique table: maps node content to existing ID
    unique: HashMap<UniqueKey, BvddId>,
    /// Computed cache: direct-mapped, keyed by (BvddId, ValueSet)
    computed_cache: Vec<Option<ComputedEntry>>,
    computed_cache_mask: usize,
    /// Well-known nodes
    false_terminal: Option<BvddId>,
    /// Stats
    pub cache_hits: u64,
    pub cache_misses: u64,
}

/// Entry in the direct-mapped computed cache
#[derive(Debug, Clone)]
struct ComputedEntry {
    node: BvddId,
    valueset: ValueSet,
    result: BvddId,
}

/// Default computed cache size (power of 2)
const DEFAULT_CACHE_SIZE: usize = 1 << 16; // 64K entries

impl Default for BvddManager {
    fn default() -> Self { Self::new() }
}

impl BvddManager {
    pub fn new() -> Self {
        Self::with_cache_size(DEFAULT_CACHE_SIZE)
    }

    pub fn with_cache_size(cache_size: usize) -> Self {
        // Ensure power of 2
        let cache_size = cache_size.next_power_of_two();
        let mut mgr = BvddManager {
            nodes: Vec::new(),
            unique: HashMap::new(),
            computed_cache: vec![None; cache_size],
            computed_cache_mask: cache_size - 1,
            false_terminal: None,
            cache_hits: 0,
            cache_misses: 0,
        };
        // Pre-allocate FALSE terminal
        let false_id = mgr.alloc_node(BvddNodeKind::Terminal { bvc: BvcId(u32::MAX) }, false, true, Canonicity::FullyCanonical);
        mgr.false_terminal = Some(false_id);
        mgr
    }

    pub fn false_terminal(&self) -> BvddId {
        self.false_terminal.unwrap()
    }

    pub fn get(&self, id: BvddId) -> &BvddNode {
        &self.nodes[id.0 as usize]
    }

    pub fn node_count(&self) -> usize {
        self.nodes.len()
    }

    /// Internal allocation without hash consing (used for bootstrapping)
    fn alloc_node(
        &mut self,
        kind: BvddNodeKind,
        can_be_true: bool,
        is_ground: bool,
        canonicity: Canonicity,
    ) -> BvddId {
        let id = BvddId(self.nodes.len() as u32);
        self.nodes.push(BvddNode { id, kind, can_be_true, is_ground, canonicity });
        id
    }

    /// Intern a node via the unique table
    fn intern(
        &mut self,
        kind: BvddNodeKind,
        can_be_true: bool,
        is_ground: bool,
        canonicity: Canonicity,
    ) -> BvddId {
        let key = UniqueKey { kind: kind.clone(), can_be_true, is_ground };
        if let Some(&id) = self.unique.get(&key) {
            return id;
        }
        let id = self.alloc_node(kind, can_be_true, is_ground, canonicity);
        self.unique.insert(key, id);
        id
    }

    /// Allocate a terminal node (hash-consed)
    pub fn make_terminal(&mut self, bvc: BvcId, can_be_true: bool, is_ground: bool) -> BvddId {
        if !can_be_true && is_ground {
            return self.false_terminal();
        }
        self.intern(
            BvddNodeKind::Terminal { bvc },
            can_be_true,
            is_ground,
            Canonicity::ModuloBvc,
        )
    }

    /// Allocate a decision node with edge merging (hash-consed)
    pub fn make_decision(
        &mut self,
        label: BvddId,
        edges: Vec<BvddEdge>,
    ) -> BvddId {
        // Step 1: Filter out empty-label edges
        let edges: Vec<BvddEdge> = edges.into_iter()
            .filter(|e| !e.label.is_empty())
            .collect();

        // Step 2: Edge merging — merge edges with the same child
        let merged = merge_edges(edges);

        // Step 3: If no edges remain, return FALSE
        if merged.is_empty() {
            return self.false_terminal();
        }

        // Step 4: If single edge with FULL label, return the child directly
        if merged.len() == 1 && merged[0].label.is_full() {
            return merged[0].child;
        }

        // Compute flags bottom-up
        let can_be_true = merged.iter().any(|e| self.get(e.child).can_be_true);
        let is_ground = merged.iter().all(|e| self.get(e.child).is_ground);

        // If can_be_true is false for all children, collapse to FALSE
        if !can_be_true {
            return self.false_terminal();
        }

        self.intern(
            BvddNodeKind::Decision { label, edges: merged },
            can_be_true,
            is_ground,
            Canonicity::ModuloBvc,
        )
    }

    /// Look up the computed cache for Solve(node, valueset)
    pub fn cache_lookup(&mut self, node: BvddId, vs: ValueSet) -> Option<BvddId> {
        let idx = cache_index(node, vs) & self.computed_cache_mask;
        if let Some(ref entry) = self.computed_cache[idx] {
            if entry.node == node && entry.valueset == vs {
                self.cache_hits += 1;
                return Some(entry.result);
            }
        }
        self.cache_misses += 1;
        None
    }

    /// Insert into the computed cache
    pub fn cache_insert(&mut self, node: BvddId, vs: ValueSet, result: BvddId) {
        let idx = cache_index(node, vs) & self.computed_cache_mask;
        self.computed_cache[idx] = Some(ComputedEntry {
            node,
            valueset: vs,
            result,
        });
    }

    /// Clear the computed cache (e.g., after garbage collection)
    pub fn cache_clear(&mut self) {
        for entry in &mut self.computed_cache {
            *entry = None;
        }
        self.cache_hits = 0;
        self.cache_misses = 0;
    }

    /// Check if a node is the FALSE terminal
    pub fn is_false(&self, id: BvddId) -> bool {
        id == self.false_terminal()
    }

    /// Check if a node is any terminal
    pub fn is_terminal(&self, id: BvddId) -> bool {
        matches!(self.get(id).kind, BvddNodeKind::Terminal { .. })
    }

    /// Get edges of a decision node
    pub fn edges(&self, id: BvddId) -> &[BvddEdge] {
        match &self.get(id).kind {
            BvddNodeKind::Decision { edges, .. } => edges,
            _ => &[],
        }
    }

    /// Restrict a BVDD to a value set (filter edges)
    pub fn restrict_to_valueset(&mut self, id: BvddId, vs: ValueSet) -> BvddId {
        if vs.is_empty() {
            return self.false_terminal();
        }
        if vs.is_full() {
            return id;
        }

        // Check cache
        if let Some(cached) = self.cache_lookup(id, vs) {
            return cached;
        }

        let result = match self.get(id).kind.clone() {
            BvddNodeKind::Terminal { .. } => id,
            BvddNodeKind::Decision { label, edges } => {
                let new_edges: Vec<BvddEdge> = edges.iter().filter_map(|e| {
                    let new_label = e.label.and(vs);
                    if new_label.is_empty() {
                        None
                    } else {
                        let child = self.restrict_to_valueset(e.child, new_label);
                        Some(BvddEdge { label: new_label, child })
                    }
                }).collect();
                self.make_decision(label, new_edges)
            }
        };

        self.cache_insert(id, vs, result);
        result
    }
}

/// Merge edges with the same child: OR their value-set labels
fn merge_edges(edges: Vec<BvddEdge>) -> Vec<BvddEdge> {
    if edges.len() <= 1 {
        return edges;
    }

    // Use HashMap for O(n) merging instead of O(n²) linear scan
    let mut map: HashMap<BvddId, ValueSet> = HashMap::with_capacity(edges.len());
    let mut order: Vec<BvddId> = Vec::with_capacity(edges.len());
    for edge in edges {
        match map.get_mut(&edge.child) {
            Some(existing) => {
                *existing = existing.or(edge.label);
            }
            None => {
                order.push(edge.child);
                map.insert(edge.child, edge.label);
            }
        }
    }
    order.into_iter().map(|child| BvddEdge {
        label: map[&child],
        child,
    }).collect()
}

/// Hash function for the computed cache
fn cache_index(node: BvddId, vs: ValueSet) -> usize {
    // FNV-like hash mixing
    let mut h: u64 = 0xcbf29ce484222325;
    h ^= node.0 as u64;
    h = h.wrapping_mul(0x100000001b3);
    for &w in &vs.bits {
        h ^= w;
        h = h.wrapping_mul(0x100000001b3);
    }
    h as usize
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_false_terminal() {
        let mgr = BvddManager::new();
        let f = mgr.false_terminal();
        assert!(!mgr.get(f).can_be_true);
        assert!(mgr.get(f).is_ground);
        assert!(mgr.is_false(f));
    }

    #[test]
    fn test_terminal_hash_consing() {
        let mut mgr = BvddManager::new();
        let t1 = mgr.make_terminal(BvcId(0), true, true);
        let t2 = mgr.make_terminal(BvcId(0), true, true);
        assert_eq!(t1, t2); // same terminal → same ID
    }

    #[test]
    fn test_false_collapse() {
        let mut mgr = BvddManager::new();
        // make_terminal with can_be_true=false, is_ground=true → FALSE
        let t = mgr.make_terminal(BvcId(99), false, true);
        assert_eq!(t, mgr.false_terminal());
    }

    #[test]
    fn test_edge_merging() {
        let mut mgr = BvddManager::new();
        let child = mgr.make_terminal(BvcId(0), true, true);
        let label_bvdd = mgr.make_terminal(BvcId(1), true, false);

        // Two edges to the same child with different labels
        let edges = vec![
            BvddEdge { label: ValueSet::singleton(1), child },
            BvddEdge { label: ValueSet::singleton(2), child },
        ];
        let dec = mgr.make_decision(label_bvdd, edges);

        // Should merge into single edge with label {1, 2}
        match &mgr.get(dec).kind {
            BvddNodeKind::Decision { edges, .. } => {
                assert_eq!(edges.len(), 1);
                assert!(edges[0].label.contains(1));
                assert!(edges[0].label.contains(2));
            }
            _ => panic!("expected decision node"),
        }
    }

    #[test]
    fn test_edge_merging_full_collapses() {
        let mut mgr = BvddManager::new();
        let child = mgr.make_terminal(BvcId(0), true, true);
        let label_bvdd = mgr.make_terminal(BvcId(1), true, false);

        // Edges that merge to FULL → should return child directly
        let edges = vec![
            BvddEdge { label: ValueSet::FULL, child },
        ];
        let dec = mgr.make_decision(label_bvdd, edges);
        assert_eq!(dec, child); // collapsed to child
    }

    #[test]
    fn test_empty_edges_filtered() {
        let mut mgr = BvddManager::new();
        let child = mgr.make_terminal(BvcId(0), true, true);
        let label_bvdd = mgr.make_terminal(BvcId(1), true, false);

        let edges = vec![
            BvddEdge { label: ValueSet::EMPTY, child }, // will be filtered
        ];
        let dec = mgr.make_decision(label_bvdd, edges);
        assert!(mgr.is_false(dec)); // no edges → FALSE
    }

    #[test]
    fn test_decision_hash_consing() {
        let mut mgr = BvddManager::new();
        let child = mgr.make_terminal(BvcId(0), true, true);
        let label = mgr.make_terminal(BvcId(1), true, false);

        let edges1 = vec![BvddEdge { label: ValueSet::singleton(5), child }];
        let edges2 = vec![BvddEdge { label: ValueSet::singleton(5), child }];

        let d1 = mgr.make_decision(label, edges1);
        let d2 = mgr.make_decision(label, edges2);
        assert_eq!(d1, d2); // same structure → same ID
    }

    #[test]
    fn test_all_false_children_collapse() {
        let mut mgr = BvddManager::new();
        let false_node = mgr.false_terminal();
        let label = mgr.make_terminal(BvcId(0), true, false);

        let edges = vec![
            BvddEdge { label: ValueSet::singleton(1), child: false_node },
            BvddEdge { label: ValueSet::singleton(2), child: false_node },
        ];
        let dec = mgr.make_decision(label, edges);
        assert!(mgr.is_false(dec)); // all children FALSE → collapse
    }

    #[test]
    fn test_flags_bottom_up() {
        let mut mgr = BvddManager::new();
        let ground_sat = mgr.make_terminal(BvcId(0), true, true);
        let non_ground = mgr.make_terminal(BvcId(1), true, false);
        let label = mgr.make_terminal(BvcId(2), true, false);

        let edges = vec![
            BvddEdge { label: ValueSet::singleton(0), child: ground_sat },
            BvddEdge { label: ValueSet::singleton(1), child: non_ground },
        ];
        let dec = mgr.make_decision(label, edges);
        assert!(mgr.get(dec).can_be_true);
        assert!(!mgr.get(dec).is_ground); // one child is not ground
    }

    #[test]
    fn test_computed_cache() {
        let mut mgr = BvddManager::new();
        let t1 = mgr.make_terminal(BvcId(0), true, true);
        let vs = ValueSet::singleton(42);

        // Cache miss initially
        assert!(mgr.cache_lookup(t1, vs).is_none());

        // Insert
        let t2 = mgr.make_terminal(BvcId(1), true, true);
        mgr.cache_insert(t1, vs, t2);

        // Cache hit
        assert_eq!(mgr.cache_lookup(t1, vs), Some(t2));
    }

    #[test]
    fn test_computed_cache_clear() {
        let mut mgr = BvddManager::new();
        let t1 = mgr.make_terminal(BvcId(0), true, true);
        let vs = ValueSet::singleton(0);
        let t2 = mgr.make_terminal(BvcId(1), true, true);

        mgr.cache_insert(t1, vs, t2);
        assert_eq!(mgr.cache_lookup(t1, vs), Some(t2));

        mgr.cache_clear();
        assert!(mgr.cache_lookup(t1, vs).is_none());
    }

    #[test]
    fn test_restrict_to_valueset() {
        let mut mgr = BvddManager::new();
        let sat_child = mgr.make_terminal(BvcId(0), true, true);
        let unsat_child = mgr.make_terminal(BvcId(1), true, true);
        let label = mgr.make_terminal(BvcId(2), true, false);

        let edges = vec![
            BvddEdge { label: ValueSet::from_range(0, 127), child: sat_child },
            BvddEdge { label: ValueSet::from_range(128, 255), child: unsat_child },
        ];
        let dec = mgr.make_decision(label, edges);

        // Restrict to {0..10} → only first edge survives
        let restricted = mgr.restrict_to_valueset(dec, ValueSet::from_range(0, 10));
        match &mgr.get(restricted).kind {
            BvddNodeKind::Decision { edges, .. } => {
                assert_eq!(edges.len(), 1);
                assert_eq!(edges[0].child, sat_child);
            }
            _ => panic!("expected decision node"),
        }
    }

    #[test]
    fn test_restrict_empty_gives_false() {
        let mut mgr = BvddManager::new();
        let t = mgr.make_terminal(BvcId(0), true, true);
        let result = mgr.restrict_to_valueset(t, ValueSet::EMPTY);
        assert!(mgr.is_false(result));
    }
}
