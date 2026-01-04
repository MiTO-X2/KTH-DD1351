% Verify the proof from the input file
verify(InputFileName) :-
    see(InputFileName),
    read(Prems), read(Goal), read(Proof),
    seen,
    valid_proof(Prems, Goal, Proof).

valid_proof(Prems, Goal, Proof) :-
    % Last element must be a non-box line [Num, Goal, Rule]
    last(Proof, Last),
    Last = [_, Goal, _],
    check_proof(Proof, Prems, []).     % start with empty Previously-checked list

% -------------------------
% Main proof traversal
% -------------------------
% empty proof ok
check_proof([], _, _).

% If the next element is a box (list whose head is an assumption line),
% validate the box recursively, then add the whole box as a single element
% to Previous (closed box).
check_proof([Box | Rest], Prems, Previous) :-
    is_box(Box),                       % detect box
    validate_box(Box, Prems, Previous),% recursively check the lines inside
    check_proof(Rest, Prems, [Box | Previous]).

% Otherwise it is a normal proof row
check_proof([Row | Rest], Prems, Previous) :-
    Row = [_, _, _],                   % ensure Row is a line, not a malformed box
    \+ is_box(Row),
    rule(Row, Prems, Previous),        % validate this row
    check_proof(Rest, Prems, [Row | Previous]).

% -------------------------
% Box helpers
% -------------------------
% A box is a non-empty list whose first element is an assumption line
is_box([[LineNum, Formula, assumption] | _]) :-
    integer(LineNum),
    Formula \= [], !.

% Validate a box: when checking the box's lines we include the box-head
% assumption as the very first 'Previous' element (so inner lines may
% reference earlier lines in the same box and also outer Previous).
validate_box([[X, P, assumption] | BoxTail], Prems, OuterPrevious) :-
    % Build the Previous list while going through the box: start with the
    % assumption itself available (so inner lines may reference it).
    check_proof(BoxTail, Prems, [[X, P, assumption] | OuterPrevious]).

% -------------------------
% Lookups
% -------------------------
% find_line(LineNum, Previous, Formula)
% Looks for a direct line [LineNum, Formula, _] in Previous.
% Previous contains only already-checked lines (not the inner contents of closed boxes).
find_line(LineNum, Previous, Formula) :-
    member([LineNum, Formula, _], Previous), !.

% find_box(StartLineNum, Previous, Box)
% Find a closed box (an element of Previous) whose head line is StartLineNum.
% The Box returned is the whole box list: [[Start,...], Inner1, Inner2, ...].
find_box(Start, Previous, Box) :-
    member(Box, Previous),
    is_box(Box),
    Box = [[Start, _, assumption] | _], !.

% last_line_of_box(Box, [LineNum, Formula, Rule])
last_line_of_box(Box, LastLine) :-
    last(Box, LastLine).

% -------------------------
% Basic rules
% -------------------------
% premise: formula must be in the premise list
rule([_, Formula, premise], Prems, _) :-
    member(Formula, Prems).

% copy: copy from a previously available line
rule([_, Formula, copy(X)], _, Previous) :-
    find_line(X, Previous, Formula).

% and-introduction: and(A,B) from lines X (A) and Y (B), (∧i x, y)
rule([_, and(A,B), andint(X,Y)], _, Previous) :-
    find_line(X, Previous, A),
    find_line(Y, Previous, B).

% and-elims (∧e1 x, ∧e2 x)
rule([_, A, andel1(X)], _, Previous) :-
    find_line(X, Previous, and(A,_)).
rule([_, B, andel2(X)], _, Previous) :-
    find_line(X, Previous, and(_,B)).

% or-intros (∨i1 x, ∨i2 x)
rule([_, or(A,_), orint1(X)], _, Previous) :-
    find_line(X, Previous, A).
rule([_, or(_,B), orint2(X)], _, Previous) :-
    find_line(X, Previous, B).

% Disjunction elimination: orel(X,Y,U,V,W), (∨e x,y–u,v–w)
% X: line with or(P,Q)
% Y: start of first subproof (assume P), its last line U must be R
% V: start of second subproof (assume Q), its last line W must be R
rule([_, R, orel(X,Y,U,V,W)], _, Previous) :-
    find_line(X, Previous, or(_,_)),
    find_box(Y, Previous, Box1),
    last_line_of_box(Box1, [U, R, _]),
    find_box(V, Previous, Box2),
    last_line_of_box(Box2, [W, R, _]).

% implication introduction (needs a box that starts at X and ends at Y), (→i x–y)
rule([_, imp(_,Q), impint(X,Y)], _, Previous) :-
    find_box(X, Previous, Box),            % find the closed box that started at X
    last_line_of_box(Box, [Y, Q, _]), !.   % last line in that box must be [Y, Q, _]

% implication elimination (→e x,y)
rule([_, Q, impel(X,Y)], _, Previous) :-
    find_line(X, Previous, P),
    find_line(Y, Previous, imp(P,Q)).

% negation introduction: assume P at X, box must end with cont at Y, (¬i x-y)
rule([_, neg(_), negint(X,Y)], _, Previous) :-
    find_box(X, Previous, Box),
    last_line_of_box(Box, [Y, cont, _]).

% negation elimination: P and neg(P) -> cont, (¬e x,y)
rule([_, cont, negel(X,Y)], _, Previous) :-
    find_line(X, Previous, P),
    find_line(Y, Previous, neg(P)).

% contradiction-elim: from cont at X infer any formula (we don't check Formula here), (⊥e x)
rule([_, _, contel(X)], _, Previous) :-
    find_line(X, Previous, cont).

% double-neg intro / elim, (¬¬i x, ¬¬e x)
rule([_, neg(neg(P)), negnegint(X)], _, Previous) :-
    find_line(X, Previous, P).
rule([_, P, negnegel(X)], _, Previous) :-
    find_line(X, Previous, neg(neg(P))).

% modus tollens: imp(P,Q) and neg(Q) -> neg(P), (MT x,y)
rule([_, neg(P), mt(X,Y)], _, Previous) :-
    find_line(X, Previous, imp(P,Q)),
    find_line(Y, Previous, neg(Q)).

% proof by contradiction (PBC): find box that assumed neg(P) at X and ended with cont at Y, (PBC x-y)
rule([_, P, pbc(X,Y)], _, Previous) :-
    find_box(X, Previous, Box),
    last_line_of_box(Box, [Y, cont, _]),
    % and the box head must be [X, neg(P), assumption]
    Box = [[X, neg(P), assumption] | _].

% LEM
rule([_, or(P, neg(P)), lem], _, _).