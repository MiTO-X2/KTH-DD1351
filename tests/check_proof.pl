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