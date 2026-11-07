# Gates: native completion root

Scope: Track E native tiers, target cells, and performance with Track F formal evidence

- [ ] G1: Every native child ledger is met with evidence
  CHECK: cargo run -p bamts-verification -- gates status
  EXPECT: GATES STATUS PASS
  EVIDENCE: pending

- [ ] G2: The native root has a closed current obligation set
  CHECK: cargo run -p bamts-verification -- completion verify --root native --aspect contract
  EXPECT: ROOT native CONTRACT PASS
  EVIDENCE: pending

- [ ] G3: The native root has no incomplete state
  CHECK: cargo run -p bamts-verification -- completion verify --root native
  EXPECT: NATIVE COMPLETE formal=PASS targets=49/49 benchmarks=9/9
  EVIDENCE: pending

- [ ] G4: The native root has no PASS-to-non-PASS transition
  CHECK: cargo run -p bamts-verification -- completion verify --root native --aspect regression
  EXPECT: ROOT native REGRESSION PASS
  EVIDENCE: pending

- [ ] G5: The native root passes its repository gate
  CHECK: just root-gate native
  EXPECT: ROOT native PASS
  EVIDENCE: pending
