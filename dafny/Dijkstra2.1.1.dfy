module DijkstraI{

class Vertex{
  var id  : int ;
  var visited: bool ;

  constructor Init()
  {
  this.visited := false;
  }
}

class Edge{
  var source : int;
  var dest: int;
  var weight : int;
}

class Graph{

  var vertices : set<Vertex>
  var edges : set<Edge>
  var d : array<int>


  predicate isValid()
  reads this, this.edges, this.vertices
  {
  ( |vertices| > 0 && |edges| > 0) &&
  (d.Length == |vertices|) &&
  (forall m | m in vertices :: ( && 0 <= m.id < d.Length )) &&
  (forall m , n | m in vertices && n in vertices && m != n :: ( m.id != n.id)) &&
  (forall e | e in edges :: e.weight > 0) &&
  (forall e | e in edges :: 0 <= e.source  < d.Length) &&
  (forall e | e in edges :: 0 <= e.dest  < d.Length) &&
  (forall e | e in edges :: e.source != e.dest) &&
  (forall e | e in edges :: !exists d | d in edges :: d != e &&  d.source == e.source && d.dest == e.dest)
  }

  predicate method hasVertex(v: Vertex)
  requires isValid()
  reads this, this.vertices, this.edges
  {
  v in vertices
  }


  method getVertex(id :int) returns (v: Vertex)
  requires isValid() && 0 <= id < d.Length
  requires isValid() ==> exists v :: v in vertices && v.id == id
  ensures isValid() && 0 <= id < d.Length 
  ensures  v.id == id
  {
	 v :| v in vertices && v.id == id;
  }

  predicate method hasEdge(u: int, v: int)
  reads this, this.edges, this.vertices
  requires isValid()
  {
  exists m | m in edges ::  m.source == u && m.dest == v && m.weight > 0
  }


   function method w(u: int, v: int): int
  reads this, this.edges, this.vertices
  requires this.isValid() && this.hasEdge(u,v)
  requires u < d.Length && v< d.Length
  {
    var f : Edge :| f in edges && f.source == u && f.dest == v;
    f.weight
  }
}

class Path{


	var pv: seq<Vertex>;


	predicate isValid(G: Graph, s: Vertex)
	reads G, G.vertices, G.d , G.edges 
	reads this, this.pv
	requires  G.isValid()
	{
		|pv| > 1 && pv[0] == s &&
		(forall v :: v in pv ==> G.hasVertex(v))  &&
		(forall b :: b in pv ==> 0 <= b.id < G.d.Length) &&
		(forall i, j :: 0 <= i < |pv| -1 && (j == i + 1) ==>
		 G.hasEdge(pv[i].id, pv[j].id))
	}


	function getPos(p : seq<Vertex>, u : Vertex) : int
	requires u in p
	{
	   var x : int :| 0 <= x < |p| && p[x] == u;
	   x
	}

	function Length(G: Graph, s: Vertex): int
	reads G, G.vertices, G.d , G.edges
	reads this, this.pv
	requires  G.isValid() && this.isValid(G,s)
	{
		Sum(0, |pv| - 1, i reads this, this.pv, G, G.edges, G.vertices, G.d
                       requires 0 <= i < |pv| - 1 && G.isValid() && this.isValid(G,s) =>
                       G.w(pv[i].id, pv[i+1].id) )
	}
  
	function Sum(lo: int, hi: int, f: int  ~> int): int
	requires forall i | lo <= i < hi :: f.requires(i)
	decreases hi - lo
	reads set i, o | lo <= i < hi && o in f.reads(i) :: o
	{
		if lo >= hi then 0
		else f(lo) + Sum(lo + 1, hi, f)
	}


	predicate isShorter(G:Graph, s:Vertex)
	reads G, G.vertices, G.d , G.edges,  this, this.pv
	requires G.isValid() && this.isValid(G,s)
	{
		G.d[pv[|pv|-1].id] > Length(G, s)
	}

	predicate isEqual(G:Graph, s:Vertex)
	reads G, G.vertices, G.d , G.edges,  this, this.pv
	requires G.isValid() && this.isValid(G,s)
	{
		G.d[pv[|pv|-1].id] == Length(G, s)
	}
}

method removeMin(G: Graph, Q: set<Vertex>) returns (min: Vertex)
requires G.isValid() && |Q| > 0
requires forall k :: k in Q ==> k in G.vertices
ensures min in G.vertices && min in Q
ensures forall k :: k in Q ==> G.d[min.id] <= G.d[k.id]
{
  var v : Vertex :| v in Q;
  var lowestDistance : int := G.d[v.id];
  var c := Q;

  while( c != {} )
  decreases c
  invariant v in Q
  invariant G.isValid() && |Q| > 0
  invariant forall l :: l in c ==> l in Q
  invariant lowestDistance == G.d[v.id]
  invariant forall k :: k in Q && k !in c ==> lowestDistance <= G.d[k.id]
  {
   var g : Vertex :| g in c;
   var gwfs := G.d[g.id];
   if(gwfs <= lowestDistance){ v := g; lowestDistance := gwfs;}
   c := c - {g};
   assert v in G.vertices;
  }
  min := v;
  return min;
}

class Dijkstra
{
	method initialisesp(G: Graph, s: Vertex)
	requires G.isValid() && G.hasVertex(s)
	requires G.isValid() ==> G.d.Length > 0
	modifies G.d, G.vertices
	ensures G.isValid() && G.hasVertex(s)
	ensures forall f :: f in G.edges ==> f.weight > 0
    ensures forall v :: v in G.vertices && v.id != s.id ==> v.visited == false
	ensures forall e, f  :: e in G.edges && 0 <= f < G.d.Length && f != s.id ==> G.d[f] >= e.weight
	ensures G.d[s.id] == 0
	{
	 var x: int := 0;
	 var swfs := G.d[s.id];
	 var loopE : set<Edge> := G.edges;
	 var c := s;
	 var infinity := 1;

	 while (loopE != {})
	 invariant G.isValid() && |G.edges| > 0
	 invariant forall j :: j in G.edges ==> j.weight >= 0
	 invariant forall l :: l in loopE ==> l in G.edges ==> l.weight > 0
	 invariant forall j :: j in loopE ==> j.weight >= 0 ==> infinity > 0 
	 invariant forall e :: e in G.edges && e !in loopE ==> infinity >= e.weight
	 invariant old(infinity) <= infinity
	 decreases loopE
	 {
	  var f : Edge :| f in loopE;
	  infinity := infinity + f.weight;
	  loopE := loopE - {f};
	 }

	 while x < G.d.Length
	 invariant G.isValid() && G.hasVertex(s) 
	 invariant 0 <= x <= G.d.Length
	 invariant infinity >= 0
	 invariant forall j :: 0 <= j < x ==> G.d[j] == infinity
	 invariant forall e :: e in G.edges ==> infinity >= e.weight
	 modifies G.d, G.vertices
	 {
	  G.d[x] := infinity;
	  x := x + 1 ;
	 }

	 forall c | c in G.vertices { c.visited := false;}
	 
	 G.d[s.id] := 0;
	 s.visited := false;
	}

	method relax(G : Graph, u: int, v: int)
	requires G.isValid() && G.hasEdge(u,v)
	requires 0 <= u < G.d.Length && 0 <= v < G.d.Length
	modifies G.d
	ensures 0 <= u < G.d.Length && 0 <= v < G.d.Length
    ensures G.isValid() && G.hasEdge(u,v)
	ensures old(G.d[v]) >= G.d[v]
	ensures old(G.d[u]) == G.d[u]
	{
	  var g : int := G.w(u,v);
	  if(G.d[v] > G.d[u] + g ) { G.d[v] := G.d[u] + g;}
	}


	method sssp(G: Graph, s: Vertex) returns (d : array<int>)
	requires G.isValid() && G.hasVertex(s)
	requires G.isValid() ==> G.vertices != {}
	modifies G, G.vertices, G.d
	ensures G.isValid() && G.hasVertex(s)
	ensures G.d.Length != 0 
	ensures old(G.d.Length) == G.d.Length
	//ensures !(exists l : Path :: l.isValid(G,s) && l.isShorter(G,s))
	{
	initialisesp(G, s);
	var settled : set<Vertex> := {};
	var unsettled : set<Vertex> := G.vertices;

    while (unsettled != {})
	invariant G.isValid() && G.hasVertex(s)
	invariant forall e | e in G.edges :: e.weight > 0
	invariant forall v | v in unsettled :: v in G.vertices
	invariant forall s | s in settled :: s in G.vertices && s.visited == true
	//for all nodes h that are settled, there doesn't exist a valid path where the last node is h and its Length is shorter than our
	//computed shortest path, in other words all settled nodes have the shortest path already estimated
	//invariant forall h | h in settled :: !(exists p: Path :: p.isValid(G,s) && p.pv[|p.pv|-1] == h && p.isShorter(G,s))
	decreases unsettled
	modifies  G.vertices, G.d
	{
	   var u : Vertex := removeMin(G, unsettled);
	   settled := settled + {u};
	   unsettled := unsettled - {u};
	   assert forall i | i in unsettled :: G.d[u.id] <= G.d[i.id];
	   var e := set v : Edge | v in G.edges && v.source == u.id;
	   var eloop := e;
	  

		while( e != {} )
		invariant G.isValid() && G.hasVertex(s)
		invariant forall a | a in e :: a in G.edges 
		invariant forall b | b in e :: 0 <= b.source < G.d.Length
		invariant forall c | c in e :: 0 <= c.dest < G.d.Length
		// if an edge that meets the criteria set by e has already been relaxed, then its new shortest path value in 
		// our G.d store of shortest paths will be shorter than the previous value stored
		//invariant forall d | d !in e && d in eloop :: G.d[d.dest] <= old(G.d[d.dest])
		modifies  G.d
		decreases e
		{
		  var l : Edge :| l in e;
		  var u : int := G.d[l.dest];
		  relax(G, l.source, l.dest);
		  var v : int := G.d[l.dest];
		  assert u >= v;
		  e := e - {l};
		}
		
		u.visited := true;
	}
	d := G.d;
	return G.d;
	}
}
}