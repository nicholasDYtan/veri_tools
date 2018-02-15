module DijkstraI{

class Vertex{
  var wfs : int ;         //Vertex contains current length from source as int, does not matter what the type of vertex is
  var pred: int ;         //Vertex Predecessor, "pi" as described in CLRS implementation
  
  constructor Init()
  modifies this
  {
  this.wfs :=900000;
  this.pred := 900000;
  } 
}

class Graph{

  var size: int;
  var edgeweights : array<array<int>>;     //weight of edges in the graph from x->y == edgeweights[x][y] 
  var vertices : array<Vertex>;            //Vertices contained in the graph, since vertices contain the wfs and pred this also 
                                           //contains our shortest paths at the end of the algorithm

  predicate hasVertex(v: int)
  reads this, this.vertices, this.edgeweights
  requires this.isValid()
  {
    0 <= v < size && 0 <= v < vertices.Length
  }

  method getVertNo(v: Vertex) returns (i: int)
  requires this.isValid() && this.verticesValid() 
  requires v != null
  {
    i := vertices.Length;
	var m := 0;
	while (m < vertices.Length)
	invariant   i <= vertices.Length 
	invariant isValid() 
	invariant verticesValid()
	{
	  if((v.wfs == vertices[m].wfs) && (v.pred == vertices[m].pred)) {i:= m;}
	  m := m + 1;
	}
  }

  predicate isValid()
  reads this, this.edgeweights, this.vertices
  {
   (
   this.size >= 2 &&
   this.edgeweights != null && 
   this.vertices != null) &&        // line that specifies that object is non-null
   this.edgeweights.Length == size &&
   this.vertices.Length == size  &&
   forall n :: 0 <= n < this.vertices.Length ==> this.vertices[n] != null &&
   forall m :: 0 <= m < this.edgeweights.Length ==> (this.edgeweights[m] != null && this.edgeweights[m].Length == size)
  }

  predicate edges()
  reads this, this.edgeweights, this.vertices
  requires this.isValid()
  reads set m | 0 <= m < edgeweights.Length :: edgeweights[m]
  {
  edgeweights != null &&
  edgeweights.Length == size &&
  forall n :: 0 <= n < edgeweights.Length ==> edgeweights[n] != null && 
  edgeweights.Length == edgeweights[n].Length && 
  edgeweights[n][n] == 0
  }

  predicate verticesValid()
  reads this, this.edgeweights, this.vertices
  requires this.isValid()                
  /*this case in particular is interesting because an update just rolled out that eliminates the need 
  to specify that the object in non-null, among other things. On the rise4fun website the earlier error now passes!*/
  reads set n | 0 <= n < vertices.Length :: vertices[n]
  {
  vertices != null &&
  vertices.Length == size &&
  forall n :: 0 <= n < vertices.Length ==> vertices[n] != null 
  }
}



class MinQueue{

    var Repre : set<Vertex>     //representing the queue of vertices using integers

	method Init()               // Initialise queue to have the empty set
	modifies this;              //since we always know the queue is never going to be greater capacity than size of graph
	{    
	 Repre := {};
	}

	method addV(vertex : Vertex)  //add an integer representing a vertex to the queue
	modifies this;
	requires vertex != null
	ensures |Repre| == old(|Repre|) +1
	{
	  Repre := Repre + {vertex};
	}

	method getSize() returns (size:int)
	{
		size := |Repre|;
		return size;
	}

	predicate method isEmpty()
	reads this, this.Repre
	{
	Repre == {}
	}

    predicate method isNotNull(R : set<Vertex>)
	reads this, this.Repre
	reads set m | m in Repre 
	{
	forall e | e in R :: e != null 
    }

	predicate isBelowLimit(R: set<Vertex>)
	requires !this.isEmpty() && this.isNotNull(R)
	reads this, this.Repre
	reads set d | d in R
	{
	forall m | m in R :: m.wfs < 900000
	}


	method removeMin() returns (v: Vertex)      // remove the smallest integer from the queue and return it
	modifies this;                              // since we represent each vertex in the Graph object as its entry in "vertices"
	requires Repre != {} && |Repre| >= 1       // we need only know which entry has the minimum wfs in the queue
	requires isNotNull(Repre) && isBelowLimit(Repre)
	ensures  |Repre| == old(|Repre|) - 1                    
	{
	  var l :| l in Repre;
      v := l;
	  var Repres : set<Vertex> := Repre;       //Repres is a copy of the real queue

	  while (Repres != {})                     //for every vertex in Repres( a copy of Repre ), find the minimum wfs vertex
		decreases |Repres|
		invariant v != null
		invariant isNotNull(Repres)
		invariant isBelowLimit(Repres)
		{
			var m :| m in Repres;
			if (m.wfs < v.wfs) { v := m; }
			Repres := Repres - {m};
		}	
	  assert v in Repre;
	  Repre := Repre - {v};
	  return v;
	}
   }

class Dijkstra{

   method InitializeSS(G : Graph, s: int)
     requires G != null && G.isValid() 
	 requires G.verticesValid() && G.hasVertex(s)
	 modifies G, G.vertices
	 modifies set m | 0 <= m < G.vertices.Length  :: G.vertices[m]
	 ensures G.isValid() && G.verticesValid() && G.hasVertex(s)
	 ensures G.vertices != null 
	 ensures G.vertices[s].wfs == 0 && G.vertices[s].pred == 900000
   {
     var x := 0 ;

	 while x < G.vertices.Length
	 modifies set m | 0 <= m < G.vertices.Length :: G.vertices[m]
	 invariant G.isValid()
	 invariant G.verticesValid()
	 invariant G.hasVertex(s)
	 invariant s < G.vertices.Length
	 {
	  G.vertices[x].wfs := 900000;
	  G.vertices[x].pred := 900000;
      x := x + 1 ;
	 }
	 G.vertices[s].wfs := 0;
	 G.vertices[s].pred := 900000;
   }

  method relax(G: Graph, u: int, v: int)
	requires G != null && G.isValid() && G.hasVertex(u) && G.hasVertex(v) && G.edges() 
	requires G.verticesValid()
	modifies G, G.edgeweights
	//modifies set m |  0 <= m < G.edgeweights.Length :: G.edgeweights[m]
	modifies set n | 0 <= n < G.vertices.Length :: G.vertices[n]
	ensures G.isValid() && G.hasVertex(u) && G.hasVertex(v) && G.verticesValid()
	ensures old(G.vertices[v].wfs) >= G.vertices[v].wfs
   {
   if (G.vertices[v].wfs > G.vertices[u].wfs + G.edgeweights[u][v])
	{
		G.vertices[v].wfs := G.vertices[u].wfs + G.edgeweights[u][v];
		G.vertices[v].pred := u;
	}
   }
 
   method sssp(G:Graph, source: int)
   requires G != null 
   requires G.isValid() && G.hasVertex(source) && G.verticesValid()
   requires G.edges()
   modifies G, G.vertices, G.edgeweights
   modifies set m | 0 <= m < G.vertices.Length :: G.vertices[m]
   {

   InitializeSS(G,source);
   var finishedVertices : set<Vertex> := {};
   var Q := new MinQueue.Init();
   var u := new Vertex.Init();
   var i := 0;
   
   
   while i < G.vertices.Length
	invariant G.isValid()
	invariant G.hasVertex(source) && G.verticesValid()
	invariant forall i :: 0 <= i < G.vertices.Length ==> G.vertices[i] != null
	invariant G.vertices.Length >= 1
	{
		Q.addV(G.vertices[i]);
		i := i + 1;
	}

	var f := Q.getSize();
	assert f >= 1;

	 
   while !Q.isEmpty()
    decreases |Q.Repre|
	invariant G.isValid()
	invariant G.hasVertex(source) && G.verticesValid()
	modifies  G.edgeweights
	modifies  Q
	{
		u:= Q.removeMin();
		finishedVertices := finishedVertices + {u};
		var tempn := G.getVertNo(u);
		var m := 0;
		while (m < G.edgeweights.Length) 
		invariant G.isValid()
		invariant G.hasVertex(tempn) && G.verticesValid()
		{
		  if (0 < G.edgeweights[tempn][m] < 900000) { relax(G, tempn, m); }
		  m := m + 1;
		}
	}

   }
   }
   
}