---- MODULE MC ----
EXTENDS learning, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
r1, r2, r3
----

\* MV CONSTANT definitions RM
const_162833156595140000 == 
{r1, r2, r3}
----

\* SYMMETRY definition
symm_162833156595141000 == 
Permutations(const_162833156595140000)
----

=============================================================================
\* Modification History
\* Created Sat Aug 07 12:19:25 CEST 2021 by rchaves
