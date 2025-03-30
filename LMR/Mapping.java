package optimaltransport;

/*import java.io.*; 
import py4j.GatewayServer;*/

import java.util.ArrayList;
import java.util.Arrays;

public class Mapping {
	private long startTime;

	/**
	 * Computes an additive approximation of the optimal transport between two discrete probability distributions, A and B, 
	 * using the Gabow-Tarjan transportation problem algorithm as a subroutine.
	 * We say that the set A contains the 'demand' vertices and the set B contains the 'supply' vertices.
	 * @param n : The number of supply and demand vertices, i.e., n = |A| = |B|.
	 * @param supplies : The probability distribution associated with the supply locations. 
	 * @param demands : The probability distribution associated with the supply locations. 
	 * Requirements: Both supplies and demands must be size n and sum to 1.
	 * @param C : An n x n cost matrix, where C[i][j] gives the cost of transporting 1 unit of mass from the ith demand vertex
	 * to the jth supply vertex.
	 * 
	 * Computes a transport plan with additive error at most delta away from the optimal and stores the transport in the
	 * 'flow' variable, which can be retieved afterwards using the 'getFlow()' method.
	 */
	public Mapping(int n, double[] supplies, double[] demands, double[][] C, double delta) {
		startTime = System.currentTimeMillis();
		
		double max = 0;
		
		for (int i = 0; i < n; i++) {
			max = Double.max(max, supplies[i]);
		}
		
		double maxCost = 0;
		for (int i = 0; i < n; i++) {
			for (int j = 0; j < n; j++) {
				maxCost = Double.max(maxCost, C[i][j]);
			}
		}
		
		//Convert the inputs into an instance of the transportation problem with integer supplies, demands, and costs.
		int[][] scaledC = new int[n][n];
		int[] scaledDemands = new int[n];
		int[] scaledSupplies = new int[n];
		double alpha = 4.*maxCost / delta;
		for (int i = 0; i < n; i++) {
			for (int j = 0; j < n; j++) {
				scaledC[i][j] = (int)(C[i][j] * alpha);
			}
			scaledDemands[i] = (int)(Math.ceil(demands[i] * alpha * n));
			scaledSupplies[i] = (int)(supplies[i] * alpha * n);
		}
	
		//Call the main Gabow-Tarjan algorithm routine to solve the scaled instance.
		//Returns a maximum-size transport plan additive error at most sum(scaledSupplies).
		GTTransport gt = new GTTransport(scaledC, scaledSupplies, scaledDemands, n);
		
		//Record the efficiency-related results of the main routine
		this.iterations = gt.getIterations();
		this.APLengths = gt.APLengths();
		this.mainRoutineTimeInSeconds = gt.timeTakenInSeconds();
		this.timeTakenAugment = gt.timeTakenAugmentInSeconds();
		
		//Get the solution for the scaled instance.
		int[][] scaledFlow = gt.getSolution();
	
		flow = new double[n][n];
		
		//Scale back flows and compute residual (leftover) supplies and demands.
		double[] residualSupply = new double[n];
		double[] residualDemand = new double[n];

		for (int i = 0; i < n; i++) {
			residualSupply[i] = supplies[i];
			residualDemand[i] = demands[i];
		}

		for (int i = 0; i < n; i++) {
			for (int j = 0; j < n; j++) {
				flow[i][j] = scaledFlow[i + n][j] / (n * alpha); 
				residualSupply[j] -= flow[i][j];
				residualDemand[i] -= flow[i][j];
			}
		}
		
		//Push back some flow incoming to demand constraints that are violated.
		for (int j = 0; j < n; j++) {
			for (int i = 0; residualDemand[j] < 0 && i < n; i++) {
				double reduction = Double.min(-residualDemand[j], flow[j][i]);
				flow[j][i] -= reduction;
				residualDemand[j] += reduction;
				residualSupply[i] += reduction;
			}
		}

		//Arbitrarily match the remaining supplies
		for (int i = 0; i < n; i++) {
			for (int j = 0; residualSupply[i] > 0 && j < n; j++) {
				double increase = Double.min(residualSupply[i], residualDemand[j]);
				flow[j][i] += increase;
				residualDemand[j] -= increase;
				residualSupply[i] -= increase;
			}
		}
		
		this.totalCost = 0;
		for (int i = 0; i < n; i++) {
			for (int j = 0; j < n; j++) {
				totalCost += flow[i][j] * C[i][j];
			}
		}
		
		timeTaken = (System.currentTimeMillis() - startTime)/1000.;
	}
	
	//A method that can be called to verify the contents of the produced flow to ensure it is feasible.
	public void verifyFlow(double[] supplies, double[] demands, double[][] flow) {	
		int n = supplies.length;
		for (int i = 0; i < n; i++) {
			double sumB = 0;//sum for flow outgoing from supply vertex i
			double sumA = 0;//sum for flow incoming to demand vertex i
			for (int j = 0; j < n; j++) {
				sumB += flow[j][i];
				sumA += flow[i][j];
			}
			double residualB = supplies[i] - sumB;
			double residualA = demands[i] - sumA;
			double threshold = 0.00001;
			if (Math.abs(residualB) > threshold) {
				System.err.println("Violation B: " + residualB + " at index " + i);
			}
			if (Math.abs(residualA) > threshold) {
				System.err.println("Violation A: " + residualA + " at index " + i);
			}
		}
	}
	
	private double mainRoutineTimeInSeconds;
	
	public double getMainRoutineTimeInSeconds() {
		return mainRoutineTimeInSeconds;
	}

	private double[][] flow;
	private double totalCost;
	private double timeTaken;
	private double timeTakenAugment;
	private int iterations;
	private int APLengths;
	

	public double[][] getFlow() {
		return flow;
	}


	public double getTotalCost() {
		return totalCost;
	}


	public double getTimeTaken() {
		return timeTaken;
	}


	public int getIterations() {
		return iterations;
	}


	public int getAPLengths() {
		return APLengths;
	}
	
	public double getTimeTakenAugment() {
		return timeTakenAugment;
	}
}


 class GTTransport {
	private int[][] CBA;
	private int[][] CAB;

	private int[] y;
	private int[][] capacityAB;
	private int[][] capacityBA;
	private boolean[] bFree;
	private boolean[] aFree;
	private int n;
	private int[] vertexVisited;
	
	private long timeTaken;
	private long timeTakenAugment;
	
	private int iterations;
	private int APLengths;
	
	//Number of calls to findAP
	private int numAPCalls = 0;
	
	// Preallocated array of size 2*n for findAP function.
	private ArrayList<Integer> path; 
	
	private int[][] finalCapacity;
	
	//Note: Does not actually compute the solution. Rather, returns the 
	//solution that was previously computed by the constructor.
	public int[][] getSolution() {
		return finalCapacity;
	}
	
	public double timeTakenInSeconds() {
		return timeTaken / 1000.;
	}
	
	public double timeTakenAugmentInSeconds() {
		return (double)timeTakenAugment / 1E9;
	}
	
	public int getIterations() {
		return iterations;
	}
	
	public int getNumAPCalls() {
		return this.numAPCalls;
	}
	
	public int APLengths() {
		return APLengths;
	}
	
	@Override
	public String toString() {
		return "GTTransport [timeTaken=" + timeTaken + ", iterations=" + iterations + ", APLengths=" + APLengths + "]";
	}
	
	
	//Solves instance of problem in constructor.
	//Solution is then recovered by calling the above "get solution" method.
	//Other relevant values can be recovered using their respective getter methods.
	//Solving problem in constructor guarantees any input instance is only
	//solved once.
	public GTTransport(int[][] C, int[] supplies, int[] demands, int n) {
		long startTime = System.currentTimeMillis();
		this.n = n;
		
		//Convention: CBA contains costs for edges directed from B to A.
		//CBA[i][j], 0 <= i,j < n, gives the cost of the edge from the
		//ith vertex of B to the jth vertex of A.
		//CAB[j][i] is the cost from the ith vertex of A to the jth vertex of B.
		//These costs are symmetric, but storing both is useful for efficiency reasons.
		//We follow this convention also for slacks, etc.
		//Note that this convention is the opposite of that used for the original Matlab implementation of this code.
		//The difference is because of how both languages store arrays (column vs. row order)
		CBA = transpose(C);
		CAB = C;		
		
		//Whether all supplies or demands of a vertex have been satisfied.
		bFree = new boolean[n];
		aFree = new boolean[n];
		
		for(int i = 0; i < n; i++) {
			bFree[i] = supplies[i] != 0;
			aFree[i] = demands[i] != 0;
		}
		
		//Dual weights for B and A
		y = new int[2*n];
		
		//Remaining "unmatched" supply or demand.
		int[] deficiencyB = supplies;
		int[] deficiencyA = demands;
		capacityAB = new int[n][n];
		capacityBA = new int[n][n];
		
		for(int i = 0; i < n; i++) {
			for(int j = 0; j < n; j++) {
				capacityBA[i][j] = Math.min(deficiencyB[i], deficiencyA[j]); 
			}
		}
		
		//Preallocate maximum AP length of 2*n
		path = new ArrayList<Integer>(2*n);
		
		//Main iteration loop. Continue executing until all supply vertices have no more residual.
		while (any(bFree)) {
			iterations++;
			//Perform Dijkstra's algorithm
			//To identify the distances lv
			//in slack from the nearest free vertex of B.
			//First n vertices are type B. 
			//Second set of n vertices are type A.
			int[] lv = new int[2*n];
			
			//The minimum distance to any free vertex of A.
			int distAF = Integer.MAX_VALUE;
			
			//For each vertex, store whether this vertex has been chosen
			//As minDist before. All such vertices have already been included
			//in the Dijkstra shortest path tree, and are final.
			boolean[] finalDist = new boolean[2*n];
			Arrays.fill(lv, Integer.MAX_VALUE);
			for (int i = 0; i < n; i++) {
				if (bFree[i]) {
					lv[i] = 0;
				}
			}
			
			//Main Dijkstra loop. Each iteration adds one vertex to the shortest
			//path tree. Total time for all iterations is O(n^2).
			//Will break out early if free vertex of A is reached.
			for (int i = 0; i < 2*n; i++) {
				//Find the next vertex to add to the shortest path tree
				int minDist = Integer.MAX_VALUE;
				int minIndex = -1; //Placeholder
				for (int v = 0; v < 2*n; v++) { 
					if (lv[v] < minDist && !finalDist[v]) {
						minDist = lv[v];
						minIndex = v;
					}
				}
				finalDist[minIndex] = true;
				
				//From the for loop condition, the early breaking out upon
				//reaching a free vertex, and the fact that the total supply is 
				//less than the total demand, there should always be an augmenting
				//path found, meaning minDist < Inf. The asserts double check this if enabled.
				assert(minIndex != -1);
				assert(minDist < Integer.MAX_VALUE);
				
				if (minIndex < n) {
					//Add a vertex of type B to the tree
					//Update distances to all neighbors in A
					for (int a = 0; a < n; a++) {
						if (capacityBA[minIndex][a] > 0) {
							int aIndex = a + n;
							int newDist = lv[minIndex] + CBA[minIndex][a] + 1 - y[minIndex] - y[aIndex];
							if (newDist < lv[aIndex]) {
								lv[aIndex] = newDist; 
							}
						}
					}
				}
				else {
					//Add a vertex of type A to the tree
					//Update distances to all neighbors in B
					int a = minIndex - n;
					if (aFree[a]) {
						distAF = lv[minIndex];
						break;
					}
					for (int b = 0; b < n; b++) {
						if (capacityAB[a][b] > 0) {
							int newDist = lv[minIndex] + y[a + n] + y[b] - CAB[a][b];
							if (newDist < lv[b]) {
								lv[b] = newDist;
							}
						}
					}
				}
			}
		
			//Since there is a free vertex of B left, there is always some AP left
			assert(distAF < Integer.MAX_VALUE);

			assert(distAF > 0); //Ensures that a maximal set of vertex-disjoint shortest augmenting paths was found last phase.
			
			//Now, perform dual adjustments 
			for (int i = 0; i < lv.length; i++) {
				int delta = Math.max(distAF - lv[i], 0);
				if (i < n) { 
					//i is a vertex of B; increase dual
					 y[i] += delta;
					 assert(y[i] >= 0);
				}
				else {
					// i is a vertex of A. Decrease dual.
					y[i] -= delta;
					assert(y[i] <= 0);
				}
			}

			//Let the admissible graph be the set of 0 slack edges.
			//Now, we iteratively execute partial DFS searches from each free
			//vertex of B to find a maximal set of vertex-disjoint admissible
			//augmenting paths.
			
			//This is used by the DFS procedure to track the
		    //largest explored neighbor index of every vertex.
		    //Following our convention, 0:n-1 -> B and n:2n-1 -> A.
			//These values persist throughout all partial DFS searches this phase
			vertexVisited = new int[2*n];
			for (int i = 0; i < n; i++) {
				vertexVisited[i] = n-1;
			}
			for (int i = 0; i < n; i++) {
				vertexVisited[i + n] = -1;
			}
			
			for (int vertex = 0; vertex < n; vertex++) {
				if (bFree[vertex]) {
					//For each free vertex, repeatedly find admissible APs
					//until no more can be found.
					while (deficiencyB[vertex] > 0 && vertexVisited[vertex] < 2*n - 1) {
						ArrayList<Integer> ap = null;
						
						ap = findAP(vertex);
						
						//Comment this out to make code faster
						//Uncomment if time taken by augmentations needs to be measured.
						//long startTimeAugment = System.nanoTime();
						if (ap.size() == 0) {
							//No AP was found. Move to next free vertex.
							break;
						}
						APLengths += ap.size() - 1;
						
						//Compute the bottleneck capacity beta: the maximum amount of flow that can be pushed
						//without violating some vertex / edge capacity constraint.
						int beta = Integer.min(deficiencyB[ap.get(0)], deficiencyA[ap.get(ap.size() - 1) - n]);
						for (int j = 0; j < ap.size() - 1; j++) {
							int u = ap.get(j);
							int v = ap.get(j + 1);			
							if (u >= n) {							
								//edge is directed from A to B
								beta = Integer.min(beta, capacityAB[u - n][v]);							
							}
							else {
								//edge is directed from B to A
								beta = Integer.min(beta, capacityBA[u][v - n]);
							}
						}
						
						//Augment along path by value beta
						//First, update the edge capacities.
						for (int j = 0; j < ap.size() - 1; j++) {
							int u = ap.get(j);
							int v = ap.get(j + 1);
							if (u >= n) {
								//edge is directed from A to B
								capacityAB[u - n][v] -= beta;
								capacityBA[v][u - n] += beta;
								if (capacityAB[u - n][v] > 0) {
									//Allow edge to be reused on future augmenting
									//paths this phase:
									vertexVisited[u] = v - 1;
								}
							}
							else {
								//edge is directed from B to A
								capacityBA[u][v - n] -= beta;
								capacityAB[v - n][u] += beta;
								if (capacityBA[u][v - n] > 0) {
									//Allow edge to be reused on future augmenting
									//paths this phase:
									vertexVisited[u] = v - 1;
								}
							}
						}
						
						//Next, update the deficiencies of the endpoints of the path
						int first = ap.get(0);
						deficiencyB[first] -= beta;
						if (deficiencyB[first] == 0) {
							bFree[first] = false;
						}
						
						int last = ap.get(ap.size() - 1) - n;
						deficiencyA[last] -= beta;
						if (deficiencyA[last] == 0) {
							aFree[last] = false;
						}
						
						//Comment this out to make code faster.
						//Uncomment if time taken by augment procedure needs to be measured.
						//timeTakenAugment += System.nanoTime() - startTimeAugment;
					}
				}
			}//End of main for loop for DFS'
			
			
		}//End of while loop (phase loop)
		
		//Finally, convert capacities to a slightly different format used
		//by the rest of the program (i.e., the Mapping class).
		
		finalCapacity = new int[2*n][2*n];
		for (int i = 0; i < n; i++) {
			for (int j = 0; j < n; j++) {
				finalCapacity[i + n][j] = capacityAB[i][j];
				finalCapacity[i][j + n] = capacityBA[i][j];
			}
		}
		
		timeTaken = System.currentTimeMillis() - startTime;
	}
	
	//Execute a partial DFS from the given vertex.
	//If an admissible AP is found, return it.
	//else, return an empty list.
	public ArrayList<Integer> findAP(int start) {
		numAPCalls++;
		//Path is a preallocated array of size 2*n
		path.clear(); 
		path.add(start);
		while (!path.isEmpty()) {
			int end = path.get(path.size() - 1);
			if (end >= n && aFree[end - n]) {
				//Found an AP
				return path; 
			}
			//Attempt to expand path
			boolean backtrack = true;
			int rangeStart = vertexVisited[end] + 1;
			int rangeEnd = end < n ? 2*n : n;
			for (int i = rangeStart; i < rangeEnd; i++) { 
				vertexVisited[end] = i;
				if (end < n) {
					//current vertex is type B
					int a = i - n;
					if (CBA[end][a] + 1 - y[end] - y[a + n] == 0 && capacityBA[end][a] > 0) {
						backtrack = false;
						//Add vertex to path
						path.add(i);
						break;
					}
				}
				else {
					//current vertex is type A
					int a = end - n;
					if (capacityAB[a][i] > 0 && y[a + n] + y[i] == CAB[a][i]) {
						backtrack = false;
						//Add vertex to path
						path.add(i);
						break;
					}
				}
			}
			if (backtrack) {
				//No more options to explore from this vertex. Remove
				//last vertex from path.
				path.remove(path.size() - 1);
			}
		
		}
		return path;
	}
	
	//Returns true if there is any instance of true in the input array.
	//Otherwise, returns false.
	static boolean any(boolean[] free) {
		for (int i = 0; i < free.length; i++) {
			if (free[i]) {
				return true;
			}
		}
		return false;
	}
	
	public static int[][] transpose(int[][] matrix){
		int[][] t = new int[matrix.length][matrix[0].length];
		for(int i = 0; i < matrix.length; i++) {
			for(int j = 0; j < matrix[0].length; j++) {
				t[j][i] = matrix[i][j];
			}
		}
		return t;
	}
	
	//Some methods for outputting matrix contents if desired.
	public static String arrToString(int[][] arr) {
		StringBuilder sb = new StringBuilder();
		for (int i = 0; i < arr.length; i++) {
			for (int j = 0; j < arr[0].length; j++) {
				sb.append(arr[i][j]);
				sb.append(' ');
			}
			sb.append('\n');
		}
		return sb.toString();
	}
	
	public static String arrToString(int[] arr) {
		StringBuilder sb = new StringBuilder();
		for (int j = 0; j < arr.length; j++) {
			sb.append(arr[j]);
			sb.append(' ');
		}
		sb.append('\n');
		
		return sb.toString();
	}
	
	
	
	
	
	
}
