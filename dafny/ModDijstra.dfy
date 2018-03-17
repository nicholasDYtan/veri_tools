module DijkstraI{

class Vertex{
  var id  : int ;
  var pred: int ;         //Vertex Predecessor, "pi" as described in CLRS implementation
  
  constructor Init()
  modifies this
  {
  this.pred := -1;
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

  method getVertexwfs(v: Vertex) returns (i: int)
  requires isValid() && hasVertex(v) && v != null
  requires hasVertex(v)  && v in vertices
  ensures d[v.id] == i
  {
   i := d[v.id];
  }

  predicate method hasEdge(u: int, v: int)
  reads this, this.edges, this.vertices
  requires isValid()
  {
  exists m | m in edges :: m != null && m.source == u && m.dest == v 
  }

  method w(u: int, v: int) returns (weight : int)
  requires this.isValid() && this.hasEdge(u,v)
  requires u < d.Length && v< d.Length
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
	modifies G.d
	ensures G!= null && G.isValid() && G.hasVertex(s)
	ensures forall m :: 0 <= m < G.d.Length && m != s.id ==> G.d[m] == -1
	ensures G.d[s.id] == 0
	{
	 var x: int := 0;
	 var swfs := G.getVertexwfs(s);
    

	 while x < G.d.Length
	 invariant G != null && G.isValid() && G.hasVertex(s)
	 invariant G.d.Length > 0 ==> G.d != null
	 invariant 0 <= x <= G.d.Length 
	 invariant forall j :: 0 <= j < x ==> G.d[j] == -1;
	 modifies G.d
	 {
	  G.d[x] := -1;
	  x := x + 1 ;
	 }
	 assert G.d[0] == -1;
	 G.d[s.id] := 0;	
	}

	method relax(G : Graph, u: int, v: int)
	requires G!= null && G.isValid() && G.hasEdge(u,v)
	requires 0 <= u < G.d.Length && 0 <= v < G.d.Length
	modifies G.d
	ensures 0 <= u < G.d.Length && 0 <= v < G.d.Length 
	ensures old(G.d[v]) >= G.d[v]
	{
	    var g : int := G.w(u,v);
		if( G.d[v] > G.d[u] + g ) { G.d[v] := G.d[u] + g;}
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
	   assert u != null;
	   assert u in unsettled;
	   unsettled := unsettled - {u};
	   var e := set v : Edge | v in G.edges && v.source == u.id && 0 <= v.dest < G.d.Length ;
	   settled := settled + {u};
	   
		while( e != {} )
		invariant G!=null && G.isValid() && G.hasVertex(s)
		invariant G.isValid() ==> forall e | e in G.edges :: e != null
		invariant forall a | a in e :: a in G.edges && a != null
		invariant G.isValid() ==> forall b | b in e :: b.source < G.d.Length
		invariant G.isValid() ==> forall c | c in e :: c.dest < G.d.Length
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