- **Fixed:**
  saving a proof whose state had gone through OCaml marshalling, as
  tools that ship proof states between processes do, silently skipped
  what the command that opened the proof had to do on save: an
  :cmd:`Instance` proved this way, for example, was declared but not
  registered as an instance. Saving such a proof is now an anomaly,
  and ``Vernacstate.is_portable`` tells whether a state can be
  marshalled without this loss
  (`#22565 <https://github.com/rocq-prover/rocq/pull/22565>`_,
  fixes `#22564 <https://github.com/rocq-prover/rocq/issues/22564>`_,
  by remix7531).
