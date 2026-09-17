(echo "Substitution can avoid branches that do not contain x")

(insert 1 (#subst (pair $0 x) x a))
(extract 1 (pair $0 a))

(echo "The explicit outer coordinate form also works")
(insert 0 (#subst $0 $0 fred))
(extract fred)
