class Vertex{
  var wfs : int ;         //Vertex contains current length from source as int, does not matter what the type of vertex is
  var pred: int ;        //Vertex Predecessor, "pi" as described in CLRS implementation
}

class Graph{

  var size: int;
  var edgeweights : array<array<int>>;     //weight of edges in the graph from x->y == edgeweights[x][y] 
  var vertices : array<Vertex>;            //Vertices contained in the graph, since vertices contain the wfs and pred this also 
                                           //contains our shortest paths at the end of the algorithm

  predicate method hasVertex(v: int)
  reads this;
  {
    0 <= v < size
  }

  predicate isValid()
  requires vertices != null && forall n :: 0 <= n < vertices.Length ==> vertices[n] != null 
  reads this, this.edgeweights, this.vertices; 
  reads set m | 0 <= m < this.vertices.Length  :: this.vertices[m]
 // reads set n | 0 <= n < this.edgeweights.Length :: this.edgeweights[n]
  {
   //edgeweights.Length == size &&
   vertices.Length == size 
  // forall x :: 0 <= x < edgeweights.Length ==> edgeweights[x].Length == edgeweights.Length &&
  // forall s, d :: 0  <= s < edgeweights.Length && 0 <= d < edgeweights[s].Length ==>  edgeweights[s][d] > 0
  }
}


	

class MinQueue{

    var Repre : set<int>

	method Init(capacity: int)
	modifies this;     //since we always know the queue is never going to be greater capacity than size of graph
	{    
	 Repre := {};
	 Repre := Repre + {capacity};
	}

	method removeMin() returns (vertex: int)
	modifies this;
	requires Repre != {};

	{
	  var c:= |Repre|;
	  var m : int;
	  var Repres : set<int> := Repre;
	  while m in Repres
	  decreases |Repres| 
	  {
	    if m <=c { c := m ;}
		Repres := Repres - {m};
	  }
	  vertex := c;
	  Repre := Repre - {vertex};
	  return vertex;
	}
   }

   class Dijkstra{

   method InitializeSS(G : Graph, s: int)
	 requires G != null && G.isValid() && G.hasVertex(s)
	 modifies G.vertices 
	 
   {
     var x := G.vertices.Length -1 ;
	 while x >= 0 {
	 G.vertices[x].wfs := 900000;
	 G.vertices[x].pred := 900000;
     x := x -1 ;
	 }
	 G.vertices[s].wfs := 0;
   }

   method relax(G: Graph, u: int, v: int, w: int)
    requires G != null && G.isValid() && G.hasVertex(u) && G.hasVertex(v)
	modifies G.edgeweights
	//reads G.edgeweights
   {
	 var x := 0;
	 while x < G.size{
	 if G.vertices[v].wfs > G.vertices[u].wfs + G.edgeweights[u][v]
	 {}
	 }
   }
   }