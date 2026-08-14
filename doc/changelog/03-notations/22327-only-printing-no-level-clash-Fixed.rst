- **Fixed:**
  An ``only printing`` :cmd:`Notation` no longer has to be declared at the
  level already attached to its notation string: such a notation adds no
  parsing rule, so the requirement was spurious. It made, for instance, VST's
  ``only printing`` notations for ``_ != _`` and ``_ == _`` (at C level 17)
  and ssreflect's parsing notations for the same strings (at level 70)
  mutually exclusive, forcing an import order upon their users. Both orders
  are now accepted; the discrepancy is reported by the new
  :warn:`notation-incompatible-level` warning. Two parsing rules for the same
  notation string at incompatible levels remain an error
  (`#22327 <https://github.com/rocq-prover/rocq/pull/22327>`_,
  fixes `#12465 <https://github.com/rocq-prover/rocq/issues/12465>`_
  and `#12589 <https://github.com/rocq-prover/rocq/issues/12589>`_
  and `#6078 <https://github.com/rocq-prover/rocq/issues/6078>`_,
  by remix7531).
- **Fixed:**
  An ``only printing`` notation is no longer taken into account when
  computing the default levels of, and checking the
  :ref:`factorization <NotationFactorization>` of, the parsing rules of
  notations declared afterwards with a common prefix. It has no parsing rule,
  so its argument levels used to leak into the grammar of these notations;
  for instance an ``only printing`` ``"a1 == a2"`` with ``a2 at level 16``
  made a subsequent parsing ``"x == y"`` at level 70 parse ``0 == 1 + 1`` as
  ``(0 == 1) + 1``
  (`#22327 <https://github.com/rocq-prover/rocq/pull/22327>`_,
  by remix7531).
