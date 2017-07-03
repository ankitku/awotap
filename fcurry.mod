module fcurry.

ty top.
ty (arr A B) :- ty A, ty B.

of (app M N) T :- of M (arr U T), of N U.
of (abs R) (arr T U) :- pi x\ (of x T => of (R x) U).
of N (all T) :- pi a\ of N (T a).
of N (T U) :- of N (all T).
% We add this since Girard's proof assumes we can always find
% at least one element in the reducibility relation
of c A :- ty A.

ins (all T) (T U).

ins* T T.
ins* T S :- ins T U, ins* U S.

step (app M N) (app M' N) :- step M M'.
step (app M N) (app M N') :- step N N'.
step (abs R) (abs R') :- pi x\ step (R x) (R' x).
step (app (abs R) N) (R N).

steps M M.
steps M N :- step M M', steps M' N.

