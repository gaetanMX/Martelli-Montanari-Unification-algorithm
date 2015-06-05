:- op(20,xfy,?=).

% Prédicats d'affichage fournis

% set_echo: ce prédicat active l'affichage par le prédicat echo
set_echo :- assert(echo_on).

% clr_echo: ce prédicat inhibe l'affichage par le prédicat echo
clr_echo :- retractall(echo_on).

% echo(T): si le flag echo_on est positionné, echo(T) affiche le termeT
%          sinon, echo(T) réussit simplement en ne faisant rien.

echo(T) :- echo_on, !, write(T).
echo(_).


%%%%%%%%%%%%% Question 1 

% regle(E,R)
regle(X?=T,rename):- var(X),var(T),!.
regle(X?=T,simplify):- var(X),atomic(T),!.
regle(X?=T,expand):- var(X),compound(T),occur_check(X,T),!.
regle(X?=T,check):- X\==T,\+occur_check(X,T),!.
regle(T?=X,orient):- nonvar(T),var(X),!.
regle(T1?=T2,decompose):- \+regle(T1?=T2,expand),!,functor(T1,F1,A1),functor(T2,F2,A2),F1==F2,A1==A2,!.
regle(T1?=T2,clash):- \+(functor(T1,F,A)=functor(T2,F,A)),!.

% occur_check(X,T): vrai si la variable X n'apparait pas dans le terme T
occur_check(X,Y):-    
      var(Y),!,X \== Y,!.
occur_check(X,Y):-
      Y =.. [_|R],
      occur_check_list(X,R).
occur_check_list(_X,[]):-!.
occur_check_list(X,[A|R]):-
      occur_check(X,A),
      occur_check_list(X,R),!.

% reduit(R,E,P,Q) 

 reduit(rename,X?=T,[X?=T|Rest],Q) :-  
  %on unifie l'equation et on s'occupe du reste Q
  X=T,Q=Rest.
 reduit(simplify,X?=T,[X?=T|Rest],Q) :-
  X=T,Q=Rest.
 reduit(expand,X?=T,[X?=T|Rest],Q) :-
  X=T,Q=Rest.
 reduit(orient,X?=T,[X?=T|Rest],Q) :-
  X=T,Q=Rest.
 reduit(decompose,X?=T,[X?=T|Rest],Q) :-
  X=..X1, %transforme une fonction ou un prédicat p(X1,..,Xn) en une liste [p,X1,..,Xn]
  delete_one(X1,X_res),  %pour supprimer le premier élément de la liste (le nom du predicat)
  T=..T1, %pareil avec la seconde partie de l'equation
  delete_one(T1,T_res),
%décompse les X1..Xn,T1..Tn en une liste tel que X1?=T1...T1?=Tn et l'ajoute au nouveau systeme
  dec_liste(X_res,T_res,Res),append(Res,Rest,Q),!. 


%predicat pour supprimer le premier élément
delete_one([_|Z],K) :- K = Z,!.
delete_one([]):- [],!.

%predicat pour décomposer : X1?=T1...T1?=Tn
dec_liste([A1|Rest1],[A2|Rest2],Res) :- dec_liste(Rest1,Rest2,Res1),append([A1?=A2],Res1,Res),!.
dec_liste([],[],Res) :- Res=Res,!.


% reduit(_,X?=T,[X?=T|Rest],Q) :-

% unifie(P)

unifie([]) :- !. 

% Parcours de la liste d'equations, on regarde à chaque fois si on peut appliquer une regle ou non
% Si oui on l'applique et on passe au reste des equations (récursion) 
unifie([X?=T|Rest]) :- 
  regle(X?=T,rename),!,
  %trace%
  echo('systeme:  '),echo([X?=T|Rest]),echo('\n'),echo('rename:   '),echo(X?=T),echo('\n'),
  %traitement
  reduit(rename,X?=T,[X?=T|Rest],Q),unifie(Q),!.

unifie([X?=T|Rest]) :- 
  regle(X?=T,simplify),!,
  %trace%
  echo('systeme:  '),echo([X?=T|Rest]),echo('\n'),echo('simplify: '),echo(X?=T),echo('\n'),
  %traitement
  reduit(simplify,X?=T,[X?=T|Rest],Q),unifie(Q),!.

unifie([X?=T|Rest]) :- 
  regle(X?=T,expand),!,
  %trace%
  echo('systeme:  '),echo([X?=T|Rest]),echo('\n'),echo('expand:   '),echo(X?=T),echo('\n'),
  %traitement
  reduit(expand,X?=T,[X?=T|Rest],Q),unifie(Q),!.

unifie([X?=T|Rest]) :- 
  regle(X?=T,check),!,
  %trace%
  echo('systeme:  '),echo([X?=T|Rest]),echo('\n'),echo('check:    '),echo(X?=T),echo('\n'),
  %traitement
  fail,!.

unifie([X?=T|Rest]) :- 
  regle(X?=T,orient),!,
  %trace%
  echo('systeme:  '),echo([X?=T|Rest]),echo('\n'),echo('orient:   '),echo(X?=T),echo('\n'),
  %traitement
  reduit(orient,X?=T,[X?=T|Rest],Q),unifie(Q),!.

unifie([X?=T|Rest]) :- 
  regle(X?=T,decompose),!,
  %trace%  
  echo('systeme:  '),echo([X?=T|Rest]),echo('\n'),echo('decompose:'),echo(X?=T),echo('\n'),
  %traitement
  reduit(decompose,X?=T,[X?=T|Rest],Q),unifie(Q),!.

unifie([X?=T|Rest]) :- 
  regle(X?=T,clash),!,
  %trace%
  echo('systeme:  '),echo([X?=T|Rest]),echo('\n'),echo('clash:    '),echo(X?=T),echo('\n'),
  %traitement
  fail,!.

%%%%%%%%%%%%%% Question 2

% unifie(P,S)

% choix_premier, on appelle unifie(P)
unifie(X,choix_premier) :- unifie(X),!.

% choix_pondere

unifie([],choix_pondere) :- !.
unifie(X,choix_pondere) :- choix_pondere(X,X,_,1),!.

%% Cette fois on regarde si on peut appliquer une regle en fonction de son poids
%% On parcourt toute la liste d'Equations pour appliquer la regle la plus prioritaire en premier
%% Si on ne peut pas appliquer les regles de plus fortes priorités on essaye d'appliquer 
%% des regles de priorités moindres


% le denier chiffre du predicat choix_pondere(_,_,_,chiffre) désigne le numéro de la priorité
% 1(clash,check) > 2(rename,simplify) > 3(orient) > 4(decompose) > 5(expand) 


% 1° clash && check
choix_pondere([X?=T|Rest],_,_,1) :- 
  regle(X?=T,clash),!,
  %trace%
  echo('systeme:  '),echo([X?=T|Rest]),echo('\n'),echo('clash:    '),echo(X?=T),echo('\n'),
  %traitement
  fail,!.

choix_pondere([X?=T|Rest],_,_,1) :- 
   regle(X?=T,check),!,
   %trace%
   echo('systeme:  '),echo([X?=T|Rest]),echo('\n'),echo('check: '),echo(X?=T),echo('\n'),
   %traitement
   fail,!.

% Si la regle ne s'applique pas on regarde les autres équations pour voir si elle s'y applique ou non
 choix_pondere([X?=T|Rest],Q,_,1) :- 
    \+regle(X?=T,check),\+regle(X?=T,clash),!,choix_pondere(Rest,Q,_,1),!.
 
% Si on a parcouru toute la liste sans pourvoir appliquer les regles d'une certaine priorité
% alors on passe aux regles de priorite moindre
 choix_pondere([],Q,_,1) :- choix_pondere(Q,Q,Q,2),! .

% 2° rename && simplify
choix_pondere([X?=T|_],Q,[X?=T|Rest],2) :- 
  regle(X?=T,rename),!,
  %trace%
  echo('systeme:  '),echo(Q),echo('\n'),echo('rename:   '),echo(X?=T),echo('\n'),
  %traitement
  reduit(rename,X?=T,[X?=T|Rest],E),choix_pondere(E,E,E,1),!.

choix_pondere([X?=T|_],Q,[X?=T|Rest],2) :-
  regle(X?=T,simplify),!,
  %trace%
  echo('systeme:  '),echo(Q),echo('\n'),echo('simplify:   '),echo(X?=T),echo('\n'),
  %traitement
  reduit(simplify,X?=T,[X?=T|Rest],E),choix_pondere(E,E,E,1),!.

choix_pondere([X?=T|Rest],Q,_,2) :-
  \+regle(X?=T,simplify),\+regle(X?=T,rename),!,append(Rest,[X?=T],Tmp),choix_pondere(Rest,Q,Tmp,2),!.

 choix_pondere([],Q,_,2) :- choix_pondere(Q,Q,Q,3),!. 

% 3° orient
choix_pondere([X?=T|_],Q,[X?=T|Rest],3) :- 
  regle(X?=T,orient),!,
  %trace%
  echo('systeme:  '),echo(Q),echo('\n'),echo('orient:   '),echo(X?=T),echo('\n'),
  %traitement
  reduit(orient,X?=T,[X?=T|Rest],E),choix_pondere(E,E,E,1),!.

choix_pondere([X?=T|Rest],Q,_,3) :-
  \+regle(X?=T,orient),!,append(Rest,[X?=T],Tmp),choix_pondere(Rest,Q,Tmp,3),!.

 choix_pondere([],Q,_,3) :- choix_pondere(Q,Q,Q,4),!. 

%4 decompose
choix_pondere([X?=T|_],Q,[X?=T|Rest],4) :- 
  regle(X?=T,decompose),!,
  %trace%
  echo('systeme:  '),echo(Q),echo('\n'),echo('decompose:   '),echo(X?=T),echo('\n'),
  %traitement
  reduit(decompose,X?=T,[X?=T|Rest],E),choix_pondere(E,E,E,1),!.

choix_pondere([X?=T|Rest],Q,_,4) :-
  \+regle(X?=T,decompose),!,append(Rest,[X?=T],Tmp),choix_pondere(Rest,Q,Tmp,4),!.

 choix_pondere([],Q,_,4) :- choix_pondere(Q,Q,Q,5),!. 

choix_pondere([X?=T|_],Q,[X?=T|Rest],5) :- 
  regle(X?=T,expand),!,
  %trace%
  echo('systeme:  '),echo(Q),echo('\n'),echo('expand:   '),echo(X?=T),echo('\n'),
  %traitement
  reduit(expand,X?=T,[X?=T|Rest],E),choix_pondere(E,E,E,1),!.

choix_pondere([X?=T|Rest],Q,_,5) :-
  \+regle(X?=T,expand),!,append(Rest,[X?=T],Tmp),choix_pondere(Rest,Q,Tmp,5),!.

 choix_pondere([],_,_,5) :- !.

%%%%%%%%%%%%% question 3

% N'affiche pas la trace d'execution
unif(P,S) :-
  clr_echo,unifie(P,S).

% affiche la trace d'execution
trace_unif(P,S) :- 
  set_echo,unifie(P,S).

%trace_unif([f(X,Y) ?= f(g(Z),h(a)), Z ?= f(Y)],choix_pondere).