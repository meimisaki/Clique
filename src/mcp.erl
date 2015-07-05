-module(mcp).
-export([start/3]).
-define(Delay, 1000).

timestamp() -> {MegaSecond, Second, MicroSecond} = now(), MegaSecond * 1000000000000 + Second * 1000000 + MicroSecond.
new_array(Size) -> array:new(Size).
new_array(Size, Default) -> array:new(Size, {default, Default}).
get(Index, List) when is_list(List) -> lists:nth(Index, List);
get(Index, Array) -> array:get(Index - 1, Array).
set(Index, Value, List) when is_list(List) -> {Head, [_Value | Tail]} = lists:split(Index -  1, List), Head ++ [Value | Tail];
set(Index, Value, Array) -> array:set(Index - 1, Value, Array).
len(List) when is_list(List) -> length(List);
len(Array) -> array:size(Array).
rev(List) when is_list(List) -> lists:reverse(List);
rev(Array) -> to_array(rev(to_list(Array))).
to_list(List) when is_list(List) -> List;
to_list(Array) -> array:to_list(Array).
to_array(List) when is_list(List) -> array:from_list(List);
to_array(Array) -> Array.
map(Function, List) when is_list(List) -> lists:map(Function, List);
map(Function, Array) -> array:map(fun(_Index, Value) -> Function(Value) end, Array).
reduce(_Function, [], Initial) -> Initial;
reduce(Function, [Head | Tail], Initial) -> reduce(Function, Tail, Function(Initial, Head));
reduce(Function, Array, Initial) -> reduce(Function, to_list(Array), Initial).
reduce(Function, [Head | Tail]) -> reduce(Function, Tail, Head);
reduce(Function, Array) -> reduce(Function, to_list(Array)).
filter(Function, List) when is_list(List) -> lists:filter(Function, List);
filter(Function, Array) -> to_array(filter(Function, to_list(Array))).
range(From, To, _Step) when From > To -> [];
range(From, To, Step) -> [From | range(From + Step, To, Step)].
range(From, To) -> range(From, To, 1).
range(From) -> range(1, From).
sort_by_weights(Any, Weights) when is_list(Weights) -> sort_by_weights(Any, to_array(Weights));
sort_by_weights([], _) -> [];
sort_by_weights([Head | Tail], Weights) ->
	sort_by_weights(filter(fun(Value) -> get(Value, Weights) =< get(Head, Weights) end, Tail), Weights) ++
	[Head | sort_by_weights(filter(fun(Value) -> get(Value, Weights) > get(Head, Weights) end, Tail), Weights)];
sort_by_weights(Array, Weights) -> to_array(sort_by_weights(to_list(Array), Weights)).

build_graph_prim(Input, Graph) ->
	Result = io:fread(Input, "", "e ~d ~d"),
	if
		Result =:= eof ->
			file:close(Input), Graph;
		true ->
			{ok, [From, To]} = Result,
			NewGraph = set(To, [From | get(To, Graph)], Graph),
			build_graph_prim(Input, set(From, [To | get(From, NewGraph)], NewGraph))
	end.
build_graph(InPath) ->
	{ok, Input} = file:open(InPath, read),
	{ok, [Number]} = io:fread(Input, "", "n ~d"),
	build_graph_prim(Input, new_array(Number, [])).

count_degrees(_Graph, [], Degrees) -> Degrees;
count_degrees(Graph, [Head | Tail], Degrees) ->
	count_degrees(Graph, Tail, set(Head, len(get(Head, Graph)), Degrees)).

calculate_cores_dec_degrees([], Degrees, _Threshould) -> Degrees;
calculate_cores_dec_degrees([Head | Tail], Degrees, Threshould) ->
	Degree = get(Head, Degrees),
	if
		Degree =:= Threshould ->
			NewDegrees = Degrees;
		true ->
			NewDegrees = set(Head, Degree - 1, Degrees)
	end,
	calculate_cores_dec_degrees(Tail, NewDegrees, Threshould).
calculate_cores(_Graph, [], _Degrees, Cores) -> Cores;
calculate_cores(Graph, [Head | Tail], Degrees, Cores) ->
	{Vertex, Vertices} = reduce(
		fun(_First = {Vertex, Vertices}, Second) ->
			Condition = get(Vertex, Degrees) > get(Second, Degrees),
			if
				Condition ->
					{Second, [Vertex | Vertices]};
				true ->
					{Vertex, [Second | Vertices]}
			end
		end,
		Tail,
		{Head, []}),
	Degree = get(Vertex, Degrees),
	NewCores = set(Vertex, Degree, Cores),
	NewDegrees = calculate_cores_dec_degrees(get(Vertex, Graph), Degrees, Degree),
	calculate_cores(Graph, Vertices, NewDegrees, NewCores).

graph_to_matrix(Graph, Array) ->
	map(
		fun(Neighbors) ->
			reduce(
				fun(Vector, Vertex) ->
					set(Vertex, true, Vector)
				end,
				Neighbors,
				Array
			)
		end,
		Graph
	).

heuristic_is_clique(_Vector, []) -> true;
heuristic_is_clique(Vector, [Head | Tail]) ->
	get(Head, Vector) =:= true andalso heuristic_is_clique(Vector, Tail).
heuristic_prim(_Graph, [], _Cores, _Matrix, Large) -> Large;
heuristic_prim(Graph, [Head | Tail], Cores, Matrix, Large = {_LargeClique, LargeLen}) ->
	Core = get(Head, Cores),
	if
		Core < LargeLen ->
			Large;
		true ->
			Neighbors = filter(
				fun(Vertex) ->
					get(Vertex, Cores) >= LargeLen
				end,
				get(Head, Graph)
			),
			NewClique = [Head | reduce(
				fun(Clique, Vertex) ->
					Condition = heuristic_is_clique(get(Vertex, Matrix), Clique),
					if
						Condition ->
							[Vertex | Clique];
						true ->
							Clique
					end
				end,
				Neighbors,
				[]
			)],
			NewLen = len(NewClique),
			if
				NewLen =< LargeLen ->
					heuristic_prim(Graph, Tail, Cores, Matrix, Large);
				true ->
					heuristic_prim(Graph, Tail, Cores, Matrix, {NewClique, NewLen})
			end
	end.
heuristic(Graph, Unordered, Cores, Array) ->
	Ordered = rev(sort_by_weights(Unordered, Cores)),
	Matrix = graph_to_matrix(Graph, Array),
	heuristic_prim(Graph, Ordered, Cores, Matrix, {[], 0}).

subgraph_prim(Graph, Unfiltered, Function) ->
	Filtered = filter(
		Function,
		Unfiltered
	),
	{reduce(
		fun(Residual, Vertex) ->
			set(
				Vertex,
				filter(
					Function,
					get(Vertex, Residual)
				),
				Residual
			)
		end,
		Filtered,
		Graph
	), Filtered}.
subgraph_assign_flags([], Flags) -> Flags;
subgraph_assign_flags([Head | Tail], Flags) ->
	subgraph_assign_flags(Tail, set(Head, true, Flags)).
subgraph_by_filter_cores(Graph, Vertices, Cores, Threshould) ->
	subgraph_prim(Graph, Vertices, fun(Vertex) -> get(Vertex, Cores) >= Threshould end).
subgraph_by_filter_vertex_prim(Graph, Vertices, Flags) ->
	subgraph_prim(Graph, Vertices, fun(Vertex) -> get(Vertex, Flags) =:= true end).
subgraph_by_filter_vertex(Graph, Vertices, Target, Array) ->
	Flags = subgraph_assign_flags(get(Target, Graph), Array),
	subgraph_by_filter_vertex_prim(Graph, Vertices, Flags).
subgraph_by_filter_vertex_contains_self(Graph, Vertices, Target, Array) ->
	Flags = subgraph_assign_flags([Target | get(Target, Graph)], Array),
	subgraph_by_filter_vertex_prim(Graph, Vertices, Flags).
subgraph_by_remove_vertex(Graph, Vertices, Target) ->
	subgraph_prim(Graph, Vertices, fun(Vertex) -> Vertex =/= Target end).

greedy_coloring_assign_flags([], _Colors, Flags) -> Flags;
greedy_coloring_assign_flags([Head | Tail], Colors, Flags) ->
	Color = get(Head, Colors),
	if
		Color =/= undefined ->
			NewFlags = set(Color, true, Flags);
		true ->
			NewFlags = Flags
	end,
	greedy_coloring_assign_flags(Tail, Colors, NewFlags).
greedy_coloring_available_color(Flags, Index) ->
	Condition = get(Index, Flags),
	if
		Condition =/= true ->
			Index;
		true ->
			greedy_coloring_available_color(Flags, Index + 1)
	end.
greedy_coloring_prim(_Graph, [], _Colors, _Array, MaxColor) -> MaxColor;
greedy_coloring_prim(Graph, [Head | Tail], Colors, Array, MaxColor) ->
	Flags = greedy_coloring_assign_flags(get(Head, Graph), Colors, Array),
	Color = greedy_coloring_available_color(Flags, 1),
	greedy_coloring_prim(Graph, Tail, set(Head, Color, Colors), Array, max(Color, MaxColor)).
greedy_coloring(Graph, Unordered, Cores, Array) ->
	Ordered = sort_by_weights(Unordered, Cores),
	greedy_coloring_prim(Graph, Ordered, Array, Array, 0).

branch_prim(_Graph, [], _Array, {Clique, Len}, Large = {_LargeClique, LargeLen}, Pid) ->
	if
		Len =< LargeLen ->
			Large;
		true ->
			Pid ! {Clique, Len},
			{Clique, Len}
	end;
branch_prim(Graph, Vertices = [_Head | _Tail], Array, {Clique, Len}, Large = {_LargeClique, LargeLen}, Pid) ->
	Degrees = count_degrees(Graph, Vertices, Array),
	Cores = calculate_cores(Graph, Vertices, Degrees, Array),
	MaxColor = greedy_coloring(Graph, Vertices, Cores, Array),
	if
		MaxColor + Len =< LargeLen ->
			Large;
		true ->
			branch(Graph, Vertices, Array, {Clique, Len}, Large, Pid)
	end.
branch(_Graph, [], _Array, {_Clique, _Len}, Large, _Pid) -> Large;
branch(Graph, Vertices = [Head | _Tail], Array, {Clique, Len}, Large = {_LargeClique, LargeLen}, Pid) ->
	Total = len(Vertices) + Len,
	if
		Total =< LargeLen ->
			Large;
		true ->
			{FirstGraph, FirstVertices} = subgraph_by_filter_vertex(Graph, Vertices, Head, Array),
			{FirstClique, FirstLen} = branch_prim(FirstGraph, FirstVertices, Array, {[Head | Clique], Len + 1}, Large, Pid),
			{SecondGraph, SecondVertices} = subgraph_by_remove_vertex(Graph, Vertices, Head),
			{_SecondClique, _SecondLen} = branch(SecondGraph, SecondVertices, Array, {Clique, Len}, {FirstClique, FirstLen}, Pid)
	end.

initial_branch_prim(Graph, Vertices, Array, Large = {_LargeClique, LargeLen}, Pid) ->
	Degrees = count_degrees(Graph, Vertices, Array),
	Cores = calculate_cores(Graph, Vertices, Degrees, Array),
	MaxCore = reduce(fun(Core, Vertex) -> max(Core, get(Vertex, Cores)) end, Vertices, 0),
	if
		MaxCore + 1 =< LargeLen ->
			Large;
		true ->
			{NewGraph, NewVertices} = subgraph_by_filter_cores(Graph, Vertices, Cores, LargeLen),
			MaxColor = greedy_coloring(NewGraph, NewVertices, Cores, Array),
			if
				MaxColor =< LargeLen ->
					Large;
				true ->
					branch(NewGraph, NewVertices, Array, {[], 0}, Large, Pid)
			end
	end.
initial_branch(Graph, Vertices, Vertex, Array, Large = {_LargeClique, LargeLen}, Pid) ->
	Total = len(get(Vertex, Graph)) + 1,
	if
		Total =< LargeLen ->
			Large;
		true ->
			{NewGraph, NewVertices} = subgraph_by_filter_vertex_contains_self(Graph, Vertices, Vertex, Array),
			initial_branch_prim(NewGraph, NewVertices, Array, Large, Pid)
	end.

maximum_clique_prim(Graph, Vertices, Array, Large = {_LargeClique, LargeLen}, Pid) ->
	Total = len(Vertices),
	if
		Total =< LargeLen ->
			Large;
		true ->
			Degrees = count_degrees(Graph, Vertices, Array),
			Vertex = reduce(
				fun(First, Second) ->
					Condition = get(First, Degrees) < get(Second, Degrees),
					if
						Condition ->
							First;
						true ->
							Second
					end
				end,
				Vertices
			),
			{NewClique, NewLen} = initial_branch(Graph, Vertices, Vertex, Array, Large, Pid),
			{NewGraph, NewVertices} = subgraph_by_remove_vertex(Graph, Vertices, Vertex),
			if
				NewLen =< LargeLen ->
					maximum_clique_prim(NewGraph, NewVertices, Array, Large, Pid);
				true ->
					maximum_clique_prim(NewGraph, NewVertices, Array, {NewClique, NewLen}, Pid)
			end
	end.
maximum_clique(Graph, Pid) ->
	Vertices = range(len(Graph)),
	Array = new_array(len(Graph)),
	Degrees = count_degrees(Graph, Vertices, Array),
	Cores = calculate_cores(Graph, Vertices, Degrees, Array),
	Large = {_LargeClique, LargeLen} = heuristic(Graph, Vertices, Cores, Array),
	Pid ! Large,
	{NewGraph, NewVertices} = subgraph_by_filter_cores(Graph, Vertices, Cores, LargeLen),
	maximum_clique_prim(NewGraph, NewVertices, Array, Large, Pid),
	Pid ! exit.

loop(_Large, _Output, Timeout) when Timeout < 0 -> ok;
loop(Large = {_LargeClique, LargeLen}, Output, Timeout) ->
	Time = timestamp(),
	receive
		{Clique, Len} ->
			if
				Len =< LargeLen ->
					loop(Large, Output, Timeout + Time - timestamp() - ?Delay);
				true ->
					io:format(Output, "new clique: ~p~n", [Len]),
					io:format(Output, "~p~n", [Clique]),
					io:format(Output, "~p~n", [timestamp()]),
					loop({Clique, Len}, Output, Timeout + Time - timestamp() - ?Delay)
			end;
		_Any ->
			ok
	after Timeout div 1000 ->
		ok
	end.

start(InPath, OutPath, Timeout) ->
	Time = timestamp(),
	{ok, Output} = file:open(OutPath, write),
	io:format(Output, "start ~p~n", [Time]),
	Graph = build_graph(InPath),
	Self = self(),
	Pid = spawn(fun() -> maximum_clique(Graph, Self) end),
	loop({[], 0}, Output, Timeout + Time - timestamp() - ?Delay),
	exit(Pid, "timeout"),
	io:format(Output, "end ~p~n", [timestamp()]),
	file:close(Output).
