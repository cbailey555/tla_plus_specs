-------------------------------- MODULE gcd --------------------------------
EXTENDS Integers

Divides(p, n) == \E q \in Int : n = q * p

DivisorsOf(n) == {p \in Int : Divides(p, n)}

SetMax(S) == CHOOSE i \in S : \A j \in S : i >= j

GCD(n, m) == SetMax(DivisorsOf(n) \cap DivisorsOf(m))


=============================================================================
\* Modification History
\* Last modified Sun Nov 11 10:14:17 CST 2018 by pnkm
\* Created Tue Nov 06 02:02:08 CST 2018 by pnkm
