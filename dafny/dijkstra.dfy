class Vertex{
  var wfs : int ;         //Vertex contains current length from source as int, does not matter what the type of vertex is
  var pred: int ;        //Vertex Predecessor, "pi" as described in CLRS implementation

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

  predicate isValid()
  reads this, this.edgeweights, this.vertices
  {
   (this.edgeweights != null && 
   this.vertices != null) &&
   this.edgeweights.Length == size &&
   this.vertices.Length == size  &&
   forall n :: 0 <= n < this.vertices.Length ==> this.vertices[n] != null &&
   forall m :: 0 <= m < this.edgeweights.Length ==> (this.edgeweights[m] != null && this.edgeweights[m].Length == size)
   /* forall h :: 0 <= h < vertices.Length ==> (vertices[h].wfs != 900000 && vertices[h].pred != 900000) &&
   forall x :: 0 <= x < edgeweights.Length ==> edgeweights[x].Length == edgeweights.Length  &&
   forall s, d :: 0  <= s < edgeweights.Length && 0 <= d < edgeweights[s].Length ==>  edgeweights[s][d] > 0 */
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
	{
	  Repre := Repre + {vertex};
	}

	method removeMin() returns (v: Vertex) // remove the smallest integer from the queue and return it
	modifies this;                              // since we represent each vertex in the Graph object as its entry in "vertices"
	requires Repre != {};                       // we need only know which entry has the minimum wfs in the queue
	{
	  var c:= 900000;                       // treat 900000 as infinity
	  var d := 900000;
	  var m := new Vertex.Init();
	  v := new Vertex.Init();
	  var Repres : set<Vertex> := Repre;   //Repres is a copy of the real queue

	  while m in Repres                 //for every integer in Repres( a copy of Repre ), find the minimum 
	  decreases |Repres| 
	  {
	    if m.wfs <=c { c := m.wfs; d:=m.pred;}
		Repres := Repres - {m};
	  }
	  v.wfs := c;  v.pred := d;   // set the return value to the minimum vertex and remove the found integer from Repre, the real queue
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
	 ensures G.vertices[s].wfs == 0 //&& G.vertices[s].wfs == 900000
   {
     assert G.vertices != null;
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
	 //assert G.vertices[s].pred == 900000;
	 G.vertices[s].wfs := 0;
   }

   method relax(G: Graph, u: int, v: int, w: int)
	reads G, G.edgeweights
	reads set m |  0 <= m < G.edgeweights.Length :: G.edgeweights[m]
	requires G != null && G.isValid() && G.hasVertex(u) && G.hasVertex(v) && G.edges()
	modifies G, G.edgeweights
	modifies set m |  0 <= m < G.edgeweights.Length :: G.edgeweights[m]
   {}
   } 