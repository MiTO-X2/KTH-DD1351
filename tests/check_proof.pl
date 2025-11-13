% This tells Prolog it’s OK for valid_rule/3 clauses to be spread across the file
:- discontiguous valid_rule/3.


% Verify the proof from the input file
verify(InputFileName) :-
    see(InputFileName),
    read(Prems), read(Goal), read(Proof),
    seen,
    valid_proof(Prems, Goal, Proof).
 

% Check if the proof is valid
valid_proof(Prems, Goal, Proof) :-
    last(Proof, [_, Goal, _]),        % Ensure the last line of the proof matches the goal
    check_proof(Proof, Prems, []).    % Check each line of the proof


% Check each line of the proof
check_proof([], _, _).
check_proof([Row | Rest], Prems, Previous) :-
    valid_rule(Row, Prems, Previous),
    check_proof(Rest, Prems, [Row | Previous]).


% Premise rule: Ensure formula is in premises
valid_rule([_, Formula, premise], Prems, _) :-
    member(Formula, Prems).


% Assumption rule, Calls check_proof on assumption box
valid_rule([[Line, Formula, assumption] | Box], Prems, Previous) :-
    check_proof(Box, Prems, [[Line, Formula, assumption] | Previous]).


% --- Helper ---
% Get the formula from a given line number
get_formula(LineNum, Previous, Formula) :-
    member([LineNum, Formula, _], Previous), !.


% --- Logical Rules ---

% Copy a formula from a previous line in the proof
valid_rule([_, Formula, copy(X)], _, Previous) :-
    get_formula(X, Previous, Formula).


% And introduction rule (∧i x, y)
% If from x we have A, and from y we have B, we can conclude and(A,B)
valid_rule([_, and(A,B), andint(X,Y)], _, Previous) :-
    get_formula(X, Previous, A),
    get_formula(Y, Previous, B).


% And elimination rules (∧e1 x)
% If from line x we have and(A,_), we can conclude A
valid_rule([_, A, andel1(X)], _, Previous) :-
    get_formula(X, Previous, and(A,_)).


% And elimination rules (∧e2 x)
% If from line x we have and(_,B), we can conclude B.
valid_rule([_, B, andel2(X)], _, Previous) :-
    get_formula(X, Previous, and(_,B)).


% Or introduction rules (∨i1 x)
% If from x we have A, we can conclude or(A, _) (for any B)
valid_rule([_, or(A,_), orint1(X)], _, Previous) :-
    get_formula(X, Previous, A).


% Or introduction rules (∨i2 x)
% If from x we have B, we can conclude or(_,B)
valid_rule([_, or(_,B), orint2(X)], _, Previous) :-
    get_formula(X, Previous, B).


% Disjunction Elimination (∨e x,y–u,v–w)
% If:
%   - Line x contains or(P,Q)
%   - From assuming P (at line y) we derive R (up to line u)
%   - From assuming Q (at line v) we derive the same R (up to line w)
% Then we can conclude R.
valid_rule([_, R, orel(X,Y,U,V,W)], _, Previous) :-
    % Line X must be or(P,Q)
    get_formula(X, Previous, or(P,Q)),

    % Find assumption/conclusion pairs for both subproofs
    get_formula(Y, Previous, P),
    get_formula(U, Previous, R1),
    get_formula(V, Previous, Q),
    get_formula(W, Previous, R2),

    % Both subproofs must conclude the same R
    R1 = R,
    R2 = R.


% Implication Elimination (→e x,y)
% If from x we have P, and from y we have imp(P,Q), then we can infer Q
valid_rule([_, Q, impel(X,Y)], _, Previous) :-
    get_formula(X, Previous, P),
    get_formula(Y, Previous, imp(P,Q)).


% Implication Introduction (→i x–y)
% If we assume P at line x, and later derive Q at line y, then we can conclude imp(P,Q)
valid_rule([_, imp(P,Q), impint(X,Y)], _, Previous) :-
    get_formula(X, Previous, P),
    get_formula(Y, Previous, Q).


% Negation Introduction (¬i x–y)
% If assuming P (line x) leads to a contradiction (line y), then infer neg(P)
valid_rule([_, neg(P), negint(X,Y)], _, Previous) :-
    get_formula(X, Previous, P),
    get_formula(Y, Previous, cont).


% Negation Elimination (¬e x,y)
% If P and ¬P are both true, then infer contradiction (cont)
valid_rule([_, cont, negel(X,Y)], _, Previous) :-
    get_formula(X, Previous, P),
    get_formula(Y, Previous, neg(P)).


% Contradiction Elimination (⊥e x)
% From a contradiction, any formula can be derived
valid_rule([_, _, contel(X)], _, Previous) :-
    get_formula(X, Previous, cont).


% Double Negation Introduction (¬¬i x)
% From P, infer ¬¬P
valid_rule([_, neg(neg(P)), negnegint(X)], _, Previous) :-
    get_formula(X, Previous, P).


% Double Negation Elimination (¬¬e x)
% From ¬¬P, infer P
valid_rule([_, P, negnegel(X)], _, Previous) :-
    get_formula(X, Previous, neg(neg(P))).


% Modus Tollens (MT x,y)
% From imp(P,Q) and ¬Q, infer ¬P
valid_rule([_, neg(P), mt(X,Y)], _, Previous) :-
    get_formula(X, Previous, imp(P,Q)),
    get_formula(Y, Previous, neg(Q)).


% Proof by Contradiction (PBC x–y)
% If assuming ¬P leads to contradiction, infer P
valid_rule([_, P, pbc(X,Y)], _, Previous) :-
    get_formula(X, Previous, neg(P)),
    get_formula(Y, Previous, cont).


% Law of Excluded Middle (LEM)
% P ∨ ¬P is always true
valid_rule([_, or(P, neg(P)), lem], _, _).
