%----------------------------------------------------------------------
% General Game Player environment for
% Methods of AI 2009
% Sophie Veres, Stefan Depeweg, Kimon Batoulis (c) 2010
%
% player implementation
%
% example: alpha-beta pruning with various heuristics
%----------------------------------------------------------------------

:- module(loisel,[ggp_loisel_player/5]).

:- dynamic(moves/1).
:- dynamic(maxUtility/1).
:- dynamic(minUtility/1).
:- dynamic(deepness/1).
:- dynamic(currentMoveList/1).
:- dynamic(min_value/1).


time_constraint :- get_time(T), st_time(TS), my_time(DT),T > ((TS +  DT / 2) +  ((TS +  DT / 2)/2)). 

ggp_loisel_player([], _Role, _Move, _Time, _MovesList) :- !.

ggp_loisel_player(State, Role, Role:Move, _Time, _MovesList) :-
  (gdl_true(control(Role), State)
   -> ignore(minimax_decision(State, Role, Move, _)) ; gdl_legal(Role,Move,State)),
  (var(Move) -> gdl_legal(Role,Move,State) ; true),   % if no moves with Utility >0 are available, just choose the next
  retractall(moves(_)),                               % make sure that the databases are cleared after each move
  retractall(maxUtility(_)),
  retractall(minUtility(_)),
  retractall(deepness(_)),
  retractall(currentMoveList(_)),
  retractall(min_value(_)).


minimax_decision(State, Role, Move, Utility) :-
  assert(deepness(-1)),
  assert(currentMoveList([])),

  once((between(1,10000,_),
    (time_2 -> true              % while still half of the time is left
             ; retractall(currentMoveList(_)),
               findall(Utility3:Move1, moves(Utility3:Move1), CurrentMoveList),   
               assert(currentMoveList(CurrentMoveList)),         % store moves already found        
               retractall(moves(_)), once(deepness(Deepness1)), retractall(deepness(_)),
               Deepness is Deepness1 + 2, assert(deepness(Deepness)),   % increase deepness
               once(max_value(State, Role, Utility, 0, Deepness, -10000, +10000)),
               ignore(min_value(B)), retractall(min_value(_)),         % check whether the tree actually is that large
               ((Utility = 100 ; var(B)) -> true ; fail)))),

  findall(MaxUtility:Move2, moves(MaxUtility:Move2), MoveList0),   % all found moves together with their utility (>0)
  retractall(moves(_)),                                            % clear database
  % remove duplicates
  (MoveList0 = [_|_] -> list_to_set(MoveList0, MoveList)                  % newest move list
                      ; currentMoveList(CurrentMoveList),                  % previous move list
                        list_to_set(CurrentMoveList, MoveList)),
    
  sort(MoveList, MovePairs1),                                        % take the best move from the whole 
  last(MovePairs1, _X:MovePair),                                      % move list      

  member(Role:Move, MovePair).


max_value(State, Role, MaxUtility, 1, _Deepness, _, _) :-   % if max terminal, compute utility    
  (no_time -> fail ; true),
  gdl_terminal(State), !,
  gdl_goal(Role, MaxUtility, State).

max_value(State, _Role, MaxUtility, 1, 0, _, _) :- !,   % if cutoff, estimate utility
  assert(min_value(1)),
  (no_time -> fail ; true),
  all_moves(State, AllMoves),
  length(AllMoves, MaxUtility).

max_value(State, Role, MaxUtility, Layer, Deepness, Alpha0, Beta0) :-   % if not terminal
  (no_time -> fail ; true),
  asserta(maxUtility(-10000)),   % initial maximum of the node
  asserta(alpha(Alpha0)),        % store the alpha/beta values which were passed by the calling predicate
  asserta(beta(Beta0)),
  all_moves(State, AllMoves),    % find all possible moves
  length(AllMoves, Length),
  between(1, Length, X),         % backtracking loop over those moves
    (no_time -> fail ; true),
    nth1(X, AllMoves, Move),     % select the next move
    successor(State, Move, Successor),   % compute the successor state resulting from that move
    once(alpha(Alpha1)),        % dig out alpha/beta values to pass them over
    once(beta(Beta1)),
    Deepness1 is Deepness - 1,
    % go down in the tree to that particular state
    once(min_value(Successor, Role, MinUtility, Deepness1, Alpha1, Beta1)),
    once(maxUtility(MaxUtilityTemp)),
    once(retract(maxUtility(_))),
    % if we are at the root and the move is not a losing move, we store it
    ((Layer=0, MinUtility > 0)
     -> assert(moves(MinUtility:Move)) ; true),

    once(beta(Beta)),
    MaxUtilityTest is max(MaxUtilityTemp, MinUtility),   % compute the new maximum (temporarily)
    (MaxUtilityTest < Beta                               % if NO cutoff
     -> MaxUtility is max(MaxUtilityTemp, MinUtility)    % the new maximum is save
      ; MaxUtility is +10000),                           % else give the node a high value
    once(alpha(AlphaTemp)), once(retract(alpha(_))),
    AlphaTest is max(MaxUtility, AlphaTemp),             % temporary new alpha value

    ((X < Length, MaxUtilityTest < Beta, AlphaTest < 100)   % while: still moves, no cutoff, no winning move found
    -> Alpha is max(MaxUtility, AlphaTemp), asserta(alpha(Alpha)),   % update alpha
       asserta(maxUtility(MaxUtility)), fail                         % store new maximum and inspect sister nodes
     ; Alpha is max(MaxUtilityTest, AlphaTemp),             % else give final alpha value (not really necessary)
       once(retract(beta(_)))),

    (no_time -> fail ; true).

min_value(State, Role, MinUtility, _Deepness, _, _) :-   % if terminal, compute utility
  (no_time -> fail ; true),
  gdl_terminal(State), !,
  gdl_goal(Role, MinUtility, State).

min_value(State, _Role, MinUtility, 0, _, _) :- !,   % if cutoff, estimate utility    
  assert(min_value(1)),
  (no_time -> fail ; true),
  all_moves(State, AllMoves),
  length(AllMoves, Length),
  MinUtility is 50 - Length.

min_value(State, Role, MinUtility, Deepness, Alpha0, Beta0) :-   % if not terminal
  (no_time -> fail ; true),
  asserta(minUtility(+10000)),   % initial minimum of the node
  asserta(alpha(Alpha0)),        % store the alpha/beta values which were passed by the calling predicate
  asserta(beta(Beta0)),
  all_moves(State, AllMoves),    % find all possible moves
  length(AllMoves, Length),
  between(1, Length, X),         % backtracking loop over those moves
    (no_time -> fail ; true),
    nth1(X, AllMoves, Move),     % select the next move
    successor(State, Move, Successor),   % compute the successor state resulting from that move
    once(alpha(Alpha1)),         % dig out alpha/beta values to pass them over
    once(beta(Beta1)),
    Deepness1 is Deepness - 1,
    % go down in the tree to that particular state
    once(max_value(Successor, Role, MaxUtility, 1, Deepness1, Alpha1, Beta1)),
    once(minUtility(MinUtilityTemp)),
    once(retract(minUtility(_))),
    
    once(alpha(Alpha)),
    MinUtilityTest is min(MinUtilityTemp, MaxUtility),    % compute the new minimum (temporarily)
    (MinUtilityTest > Alpha                               % if NO cutoff
     -> MinUtility is min(MinUtilityTemp, MaxUtility)     % the minimum is save
      ; MinUtility is -10000),                            % else assign a low value
    once(beta(BetaTemp)), once(retract(beta(_))),
    BetaTest is min(MinUtility, BetaTemp),                % temporary new beta value

    ((X < Length, MinUtilityTest > Alpha, BetaTest > 0)   % while: still moves, no cutoff, no losing move
    -> Beta is min(MinUtility, BetaTemp), asserta(beta(Beta)),   % update beta value
       asserta(minUtility(MinUtility)), fail                     % store new minimum and inspect sister nodes  
     ; Beta is min(MinUtilityTest, BetaTemp),                    % else give final beta value (not really necessary)
       once(retract(alpha(_)))),

    (no_time -> fail ; true).


% find all possible moves to a given state
all_moves(State, AllMoves) :-
  findall(Moves, gdl_legal(Moves, State), AllMoves).

% compute the successor state to a given move
successor(State, Moves, Successor) :-
  ggp_next_state(State, Moves, Successor).
