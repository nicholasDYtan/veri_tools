module DijkstraI{

class Vertex{
  var id  : int ;
  var visited: bool ;

  constructor Init()
  modifies this
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
  (d != null && |vertices| > 0 && |edges| > 0) &&
  (d.Length == |vertices|) &&
  (forall m | m in vertices :: (m != null && 0 <= m.id < d.Length )) &&
  (forall m , n | m in vertices && n in vertices && m != n :: (m != null && n != null && m.id != n.id)) &&
  (forall e | e in edges :: e != null) &&
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
  ensures isValid() && 0 <= id < d.Length && v != null
  ensures  v.id == id
  {
	 v :| v in vertices && v.id == id;
  }

  predicate method hasEdge(u: int, v: int)
  reads this, this.edges, this.vertices
  requires isValid()
  {
  exists m | m in edges :: m != null && m.source == u && m.dest == v && m.weight > 0
  }

  method w(u: int, v: int) returns (weight : int)
  requires this.isValid() && this.hasEdge(u,v)
  requires u < d.Length && v< d.Length
  ensures weight >= 0
  {
		var f : Edge :| f in edges && f !=null && f.source == u && f.dest == v;
		weight := f.weight;
  }
}

method removeMin(G: Graph, Q: set<Vertex>) returns (min: Vertex)
requires G != null && G.isValid() && |Q| > 0
requires forall k :: k in Q ==> k in G.vertices
ensures min in G.vertices && min in Q
ensures min != null
ensures forall k :: k in Q ==> G.d[min.id] <= G.d[k.id]
{
  var v : Vertex :| v in Q;
  var lowestDistance : int := G.d[v.id];
  var c := Q;

  while( c != {} )
  decreases c
  invariant v in Q
  invariant G != null && G.isValid() && |Q| > 0
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
	requires G != null && G.isValid() && G.hasVertex(s)
	requires G.isValid() ==> G.d.Length > 0
	modifies G.d, G.vertices
	ensures G!= null && G.isValid() && G.hasVertex(s)
	ensures forall f :: f in G.edges ==> f.weight > 0
    ensures forall v :: v in G.vertices && v.id != s.id ==> v.visited == false
	ensures G.d[s.id] == 0
	{
	 var x: int := 0;
	 var swfs := G.d[s.id];
	 var loopE : set<Edge> := G.edges;
	 var c := s;
	 var infinity := 1;

	 while (loopE != {})
	 invariant G != null && G.isValid() && |G.edges| > 0
	 invariant forall j :: j in G.edges ==> j.weight > 0
	 invariant forall l :: l in loopE ==> l in G.edges ==> l.weight > 0
	 invariant old(infinity) <= infinity
	 decreases loopE
	 {
	  var f : Edge :| f in loopE;
	  infinity := infinity + f.weight;
	  loopE := loopE - {f};
	 }

	 while x < G.d.Length
	 invariant G != null && G.isValid() && G.hasVertex(s) 
	 invariant G.d.Length > 0 ==> G.d != null
	 invariant 0 <= x <= G.d.Length
	 invariant forall j :: 0 <= j < x ==> G.d[j] == infinity
	 //invariant forall e :: e in G.edges ==> infinity > e.weight
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
	requires G!= null && G.isValid() && G.hasEdge(u,v)
	requires 0 <= u < G.d.Length && 0 <= v < G.d.Length
	modifies G.d
	ensures 0 <= u < G.d.Length && 0 <= v < G.d.Length
    ensures G != null && G.isValid() && G.hasEdge(u,v)
	ensures old(G.d[v]) >= G.d[v]
	{
	  var g : int := G.w(u,v);
	  if(G.d[v] > G.d[u] + g ) { G.d[v] := G.d[u] + g;}
	}


	method sssp(G: Graph, s: Vertex) returns (d : array<int>)
	requires G != null && G.isValid() && G.hasVertex(s)
	requires forall e | e in G.edges :: e != null
	requires G.isValid() ==> forall e | e in G.edges :: e!=null
	requires G.isValid() ==> G.vertices != {}
	modifies G, G.vertices, G.d
	ensures G != null && G.isValid() && G.hasVertex(s)
	ensures G.d.Length != 0 ==> d != null
	ensures d.Length == G.d.Length
	{
	initialisesp(G, s);
	var settled : set<Vertex> := {};
	var unsettled : set<Vertex> := G.vertices;

	while (unsettled != {})
	invariant G!=null && G.isValid() && G.hasVertex(s)
	invariant forall e | e in G.edges :: e != null
	invariant forall v | v in unsettled :: v in G.vertices
	invariant G.d != null
	decreases unsettled
	modifies  G.vertices, G.d
	{
	 var u : Vertex := removeMin(G, unsettled);
     u.visited := true;
	   unsettled := unsettled - {u};
	   var e := set v : Edge | v in G.edges && v.source == u.id && v.weight > 0  && 0 <= v.dest < G.d.Length ;
	   settled := settled + {u};

		while( e != {} )
		invariant G!=null && G.isValid() && G.hasVertex(s)
		invariant G.isValid() ==> forall e | e in G.edges :: e != null
		invariant forall a | a in e :: a in G.edges && a != null
		invariant G.isValid() ==> forall b | b in e :: 0 <= b.source < G.d.Length
		invariant G.isValid() ==> forall c | c in e :: 0 <= c.dest < G.d.Length
		modifies  G.d
		decreases e
		{
		  var l : Edge :| l in e;
		  relax(G, l.source, l.dest);
		  e := e - {l};
		}
	}
	d := G.d;
	assert G.d != null;
	assert d != null;
	return G.d;
	}
}
}
