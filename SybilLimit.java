/**
 *==========================================
 * @author Abedelaziz Mohaisen and Huy Tran
	University of Minnesota - Twin cities
	Computer Science and Engineering Department
	mohaisen@cs.umn.edu and huy@cs.umn.edu
	All rights are reseved
 */
/**
 Description: this is an implementation of similarity-biased SybilLimit.

 Citations where used:
    The orignal work is due to Haifeng Yu from National University of Singapore. Please cite him where used as:
    Haifeng Yu, Phillip B. Gibbons, Michael Kaminsky, Feng Xiao: SybilLimit: A Near-Optimal Social Network Defense against Sybil Attacks. IEEE Symposium on Security and Privacy 2008: 3-17

    My works that make use of this code (or modifications of it) are in :
    - Abedelaziz Mohaisen, Nicholas Hopper, Yongdae Kim: Keep your friends close: Incorporating trust into social network-based Sybil defenses. INFOCOM 2011: 1943-1951
    - Abedelaziz Mohaisen, Aaram Yun, Yongdae Kim: Measuring the mixing time of social graphs. Internet Measurement Conference 2010: 383-389

    WARNING: the code is poorly documented. I make the assumption that you know how SybilLimit works.

*/

import java.io.*;
import java.util.*;

public class SybilLimit {
        public HashMap<Integer, LinkedList<Integer>> graph;
        public HashMap<Integer, LinkedList<String>> tails;
        public HashSet<Integer> Sample;
		
		public HashMap<Integer, Integer> region;
		public LinkedList<Integer> attackers;
		/**
         * Total number of pairs of suspect-verifier
         */
        public long totalPairs;
        /**
         * The total number of accepted suspects
         */		
        public long servedNodes;
		/**
         * Unaccepted suspects
         */
        public long unservedNodes;
		/**
         * The percent of served suspects
         */
        public double servedPercent;
		
		public long escapeNodes;
		public double escapePercent;


		/**
         * The network information, with routing table
         */
        public HashMap<Integer, Node> Network;
		/**
         * random number generator
         */
        public Random rnd;
		/**
         * the input file name (includes edge-list)
         */
        public String filename;
		/**
         * random walk length
         */
        int RWL;

		/**
         * Constructor, takes file name and sample size as input
         * Initializes the graph, tails, network, sample, and file name and
         * loads the graph and makes a sample.
         * @param fn
         * @param ss
         */
        public SybilLimit(String fn, int ss){
            graph = new HashMap<Integer, LinkedList<Integer>>();
            tails = new HashMap<Integer, LinkedList<String>>();
            Network = new HashMap<Integer, Node>();
            Sample = new HashSet<Integer>();
			region = new HashMap<Integer, Integer>();
			attackers = new LinkedList<Integer>();
            filename = fn;
            rnd = new Random();
            this.loadGraph();
            this.makeSample(ss);
            this.totalPairs = (this.Sample.size())*(this.Sample.size()-1);
        }

		/**
         * Call computations of the all tails and utility count
         * @param rwl
         */
        public void run(int rwl){
            RWL = rwl;
            this.computeAllTailsX();
            this.countUtility();
        }

		/**
         * Loads the graph from the graph file.
         */
        public void loadGraph(){
            try{
                BufferedReader in = new BufferedReader(new FileReader(filename));
                String line ="";
                int v1;
                int v2;
                while(in.ready()){
                    line = in.readLine();
                    v1 = Integer.parseInt(line.trim().split(" ")[0].trim());
                    v2 = Integer.parseInt(line.trim().split(" ")[1].trim());
                    if(graph.containsKey(v1)){
                        if(!graph.get(v1).contains(v2)){
                            graph.get(v1).add(v2);
                        }
                    }else{
                        LinkedList<Integer> tmp = new LinkedList<Integer>();
                        tmp.add(v2);
                        graph.put(v1, tmp);
                    }
                    if(graph.containsKey(v2)){
                        if(!graph.get(v2).contains(v1)){
                            graph.get(v2).add(v1);
                        }
                    }else{
                        graph.put(v2, new LinkedList<Integer>());
                        graph.get(v2).add(v1);
                    }
                }
            }catch(Exception e){e.printStackTrace();}
        }
		
		// BEGIN ESCAPE MODULE
		/**
         * Puts attackers into the graph, calculates the escape rate based on random walks performing
		 * function, then removes attackers from the graph.
		 * Input: rwl - random walk length
		 *		  clusters - number of attacker clusters
		 *		  size - size of each cluster
		 *		  edges - number of attack edges per cluster
         */
		public void escapeRun(int rwl){
			RWL = rwl;
			this.calculateEscapeRate();
		}
		
		/**
         * Puts attackers into the graph.
		 * Input: clusters - number of attacker clusters
		 *		  size - size of each cluster
		 *		  edges - number of attack edges per cluster
         */
		public void makeAttackers(int clusters, int size, int edges){
			int v_id=0;
			for (int node: graph.keySet())
				if (node > v_id) v_id = node;
			int honestMark = v_id;
			int v1=0, v2=0;
			int ranP = 0;
			int numberOfNodes = graph.keySet().size();
			Integer[] honestNodes = new Integer[graph.keySet().size()];
			honestNodes = graph.keySet().toArray(honestNodes);
			for (int i=0; i<clusters; i++){
				for (int j=1; j<size; j++)
					for (int k=j+1; k<=size; k++){
						v1 = v_id+j; v2 = v_id+k;
						if (!graph.containsKey(v1)) graph.put(v1, new LinkedList<Integer>());
						graph.get(v1).add(v2);
						if (!graph.containsKey(v2)) graph.put(v2, new LinkedList<Integer>());
						graph.get(v2).add(v1);
					}
				v1 = v_id+1;
				for (int j=0; j<edges; j++){
					ranP = rnd.nextInt(numberOfNodes);
					while (graph.get(v1).contains(honestNodes[ranP]))
						ranP = rnd.nextInt(numberOfNodes);
					graph.get(v1).add(honestNodes[ranP]);
					graph.get(honestNodes[ranP]).add(v1);
				}
				for (int j=0; j<size; j++){
					v_id++;
					attackers.add(v_id);
				}
			}
			for (int node: graph.keySet())
				if (node > honestMark) region.put(node, 1);
				else region.put(node, 0);
		}
		
		/**
         * Removes attackers from the graph, brings the graph back to the original state.
         */
		public void removeAttackers(){
			int numberOfAttacker=attackers.size();
			for (int attacker: attackers)
				for (int node: graph.get(attacker))
					graph.get(node).removeLast();
			for (int attacker: attackers)
				graph.remove(attacker);
			attackers.clear();
			region.clear();
		}
		
		/**
         * Calculates the escape rate based on random walks performing function.
         */
		public void calculateEscapeRate(){
			int r = this.computeR(4);

            //print("r",r);

            //initialize the tails;
            /*for(int node: Sample){
                tails.put(node, new LinkedList<String>());
            }*/
			int escapeCount=0;
            // perform r different s-instances.
            for(int i =0; i<r;i++){
                //print("i",i);
                this.buildRoutingTables();
                for(int node: Sample){
                    Node tNode = Network.get(node);
                    Integer[] tmpArray = new Integer[tNode.routingTable.keySet().size()];
                    int tnode = tNode.routingTable.keySet().toArray(tmpArray)[rnd.nextInt(tmpArray.length)];

                    Node currentNode;
                    currentNode = tNode;
                    Node nextNode;
                    Node prevNode;
                    int ctr;
                    nextNode = Network.get(tnode);
					if (region.get(tnode) == 1) escapeCount++;
					else {
						ctr = 0;
						ctr++;
						while(ctr<RWL){
							prevNode = currentNode;
							currentNode = nextNode;
							nextNode = Network.get(currentNode.routingTable.get(prevNode.ID));
							if (region.get(nextNode.ID) == 1){
								escapeCount++;
								break;
							}
							ctr++;
						}
					}
                    //tails.get(node).add(currentNode.ID+":"+nextNode.ID);
                }
            }
			
			long walkCount=r*Sample.size();
			System.out.print("\tEscape count:");
			System.out.print("\t");
			System.out.println(Integer.toString(escapeCount));
			System.out.print("\tWalk count:");
			System.out.print("\t");
			System.out.println(Long.toString(walkCount));
			escapeNodes = escapeCount;
			escapePercent = (double)escapeNodes/walkCount;
		}
		// END ESCAPE MODULE

		/**
         * Builds the routing tables of the different nodes.
         * uses the knuth shuffle.
         */
		public void buildRoutingTables(){
            for(int node: graph.keySet()){
                LinkedList<Integer> tmp = graph.get(node);
                int j = 0;
                Integer[] source = new Integer[tmp.size()];
                source = tmp.toArray(source);
                for(int i = source.length; i>1; i--){
                    j = rnd.nextInt(i);
                    int s1 = source[j];
                    source[j] = source[i-1];
                    source[i-1] = s1;
                }
                HashMap<Integer, Integer> tmpMap = new HashMap<Integer,Integer>();
                for(int i = 0; i<tmp.size(); i++){
                    tmpMap.put(tmp.get(i), source[i]);
                }
                this.Network.put(node, new Node(node, tmpMap));
            }

        }

		/**
         * Computes the number of edges of the graph.
         * @return
         */
        public int getNumberOfEdges(){
            int result =0;
            for(int tnode: graph.keySet()){
                result = result+this.graph.get(tnode).size();
            }

            return result/2;
        }

		/**
         * Computes R, which is roughly r0*sqrt(m).
         * @param r0
         * @return
         */
        public int computeR(int r0){
            double r = 0;
                r =r0*Math.sqrt(this.getNumberOfEdges());
            return (int)Math.ceil(r);
        }

		/**
         * makes a sample of size samplesize.
         * by randomly selecting them from the graph
         * @param samplesize
         */
        public void makeSample(int samplesize){
            Integer[] tmpArray = new Integer[graph.keySet().size()];
            tmpArray = graph.keySet().toArray(tmpArray);
            while(this.Sample.size()!=samplesize){
                this.Sample.add(tmpArray[rnd.nextInt(tmpArray.length)]);
            }
        }

		/**
         * Perform random walks from each node in the sample to compute the last
         * edge of the walk, as a tail and register it in the tails set of that node.
         */
        public void computeAllTailsX(){
            int r = this.computeR(4);

            //print("r",r);

            //initialize the tails;
            for(int node: Sample){
                tails.put(node, new LinkedList<String>());
            }
            // perform r different s-instances.
            for(int i =0; i<r;i++){
                //print("i",i);
                this.buildRoutingTables();
                for(int node: Sample){
                    Node tNode = Network.get(node);
                    Integer[] tmpArray = new Integer[tNode.routingTable.keySet().size()];
                    int tnode = tNode.routingTable.keySet().toArray(tmpArray)[rnd.nextInt(tmpArray.length)];

                    Node currentNode;
                    currentNode = tNode;
                    Node nextNode;
                    Node prevNode;
                    int ctr;
                    nextNode = Network.get(tnode);
                    ctr = 0;
                    ctr++;
                    while(ctr<RWL){
                        prevNode = currentNode;
                        currentNode = nextNode;
                        nextNode = Network.get(currentNode.routingTable.get(prevNode.ID));
                        ctr++;
                    }
                    tails.get(node).add(currentNode.ID+":"+nextNode.ID);
                }

            }
        }

		/**
         * Printing all contents of the nodes.as
         */
        public void dump(){
            for(int nodeID: this.Network.keySet()){
                System.out.println(Network.get(nodeID).toString());
            }
        }

		/**
         * compute the utulity by counting the number of accepted nodes,
         * and the remaining are the rejected ones.
         */
        public void countUtility(){
            int ctrOK = 0;
            int j = 0;
            boolean flag=false;
            for(int snode: tails.keySet()){
                for(int vnode: tails.keySet()){
                    if(vnode!=snode){
                        int i =0;
                        flag = false;
                        while(flag==false && i<tails.get(snode).size()){
                            if(tails.get(vnode).contains(tails.get(snode).get(i))){
                                j++;
                                print("j",j);
                                ctrOK++;
                                flag = true;
                            }
                            i++;
                        }
                    }
                }
            }
            this.servedNodes = ctrOK;
            this.servedPercent = (double)this.servedNodes/this.totalPairs;
            //System.out.println("Served:\t  "+ctrOK);
        }

		/**
         * Sums the degrees of the nodes (the total number of edges, routing entries, etc)
         * @param graph
         */
        public void sumMap(HashMap<Integer, LinkedList<Integer>> graph){
            int res = 0;
            for(int node: graph.keySet()){
                res = res+graph.get(node).size();
            }
            System.out.println("Sum:\t"+res);
        }

		/**
         * a utility function to print a string and an integer.
         * @param s1
         * @param s2
         */
        public static void print(String s1, int s2){
            System.out.println(s1+":\t"+s2);
        }

		/**
         * print all tails of the sample.
         */
        public void printTails(){
            for(int node: tails.keySet()){
                System.out.print(node+"\t");
                for(int i =0;i<tails.get(node).size();i++){
                    System.out.print(tails.get(node).get(i)+" ");
                }
                System.out.println("");
            }
        }

		/**
         * prints all nodes contents.
         */
        public void printNodes(){
            String res ="";
            for(int node:Network.keySet()){
                res = res+"\n"+node;
                HashMap<Integer, Integer> tmp = Network.get(node).routingTable;
                for(int src: tmp.keySet()){
                    res = res+"\n"+ src+"\t"+ tmp.get(src);
                }
            }
            System.out.println(res);
        }

		/**
         * the main function.
         * @param argv
         */
        public static void main(String argv[]){
            //SybilLimitBuilder sybil = new SybilLimitBuilder(10,"FBB010K.txt");
            //SybilLimitBuilder sybil = new SybilLimitBuilder(10,"phy1adj1k.txt");
            String inFile = argv[0].trim();
			//int numberOfClusters = Integer.parseInt(argv[1].trim());
			//int clusterSize = Integer.parseInt(argv[2].trim());
			//int el = Integer.parseInt(argv[3].trim());

            //String inFile = "data.tex";
            //String inFile = "phy1adj1k.txt";
            String outFile = "plain_"+inFile;
			
			String line = "";
			int RWLInitial = 0;
			int RWLStep = 0;
			int RWLFinal = 0;
			int gInitial = 0;
			int gStep = 0;
			int gFinal = 0;
			int attackers = 0;
			int trial = 0;
			try{
				BufferedReader ins = new BufferedReader(new FileReader("setting.plain"));
				
				line = ins.readLine();
				trial = Integer.parseInt(line.split(":")[1].trim());

				line = ins.readLine();
				RWLInitial = Integer.parseInt(line.split(":")[1].trim());
				RWLStep = Integer.parseInt(line.split(":")[2].trim());
				RWLFinal = Integer.parseInt(line.split(":")[3].trim());

				line = ins.readLine();
				gInitial = Integer.parseInt(line.split(":")[1].trim());
				gStep = Integer.parseInt(line.split(":")[2].trim());
				gFinal = Integer.parseInt(line.split(":")[3].trim());
				
				line = ins.readLine();
				attackers = Integer.parseInt(line.split(":")[1].trim());

			} catch (Exception e){
				e.printStackTrace();
				System.exit(-1);
			}
			
			HashMap<Integer, HashMap<Integer, Long>> averageData = new HashMap<Integer, HashMap<Integer, Long>>();
			for (int el=gInitial; el<=gFinal; el+=gStep){
				averageData.put(el, new HashMap<Integer, Long>());
				for (int wl=RWLInitial; wl<=RWLFinal; wl+=RWLStep)
					averageData.get(el).put(wl, (long)0);
			}
			
			String header = "";
			for (int wl=RWLInitial; wl<=RWLFinal; wl+=RWLStep)
				header = header+"\t"+Integer.toString(wl);
			header += "\n";
			
			long tempE = 0;
            
			String str = "";
            try{
                BufferedWriter fout = new BufferedWriter(new FileWriter(outFile));
                SybilLimit sybil = new SybilLimit(inFile,100);
				for (int t=0; t<trial; t++){
					fout.write(header);
					fout.flush();
					for (int el=gInitial; el<=gFinal; el+=gStep){
						sybil.makeAttackers(attackers, 2, el/attackers);
						str = Integer.toString(el);
						for (int wl=RWLInitial; wl<=RWLFinal; wl+=RWLStep){
							System.out.println("g: "+Integer.toString(el)+"\tRWL: "+Integer.toString(wl));
							sybil.escapeRun(wl);
							str = str + "\t" + Long.toString(sybil.escapeNodes);
							tempE = averageData.get(el).get(wl);
							tempE += sybil.escapeNodes;
							averageData.get(el).put(wl, tempE);
						}
						str += "\n";
						fout.write(str);
						fout.flush();
						sybil.removeAttackers();
					}
				}
				fout.write(header);
				fout.flush();
				for (int el=gInitial; el<=gFinal; el+=gStep){
					str = Integer.toString(el);
					for (int wl=RWLInitial; wl<=RWLFinal; wl+=RWLStep)
						str = str + "\t" + Double.toString((double)averageData.get(el).get(wl)/trial);
					str += "\n";
					fout.write(str);
					fout.flush();
				}
                fout.close();
            } catch (Exception e){
				e.printStackTrace();
                System.exit(-1);
            }
        }
    }

