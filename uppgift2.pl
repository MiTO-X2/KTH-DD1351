% remove_duplicates(InputList, ResultList)
remove_duplicates(List, Result) :-
    remove_duplicates_acc(List, [], Result).

% Base case: empty input list
remove_duplicates_acc([], _, []) :- !.

% Case 1: Head already seen, skip it
remove_duplicates_acc([H|T], Seen, Result) :-
    member(H, Seen), !,
    remove_duplicates_acc(T, Seen, Result).

% Case 2: Head not seen, keep it
remove_duplicates_acc([H|T], Seen, [H|Result]) :-
    remove_duplicates_acc(T, [H|Seen], Result).








