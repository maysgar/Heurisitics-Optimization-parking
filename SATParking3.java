import java.io.BufferedReader;
import java.io.FileReader;
import java.io.File;
import java.io.IOException;
import org.jacop.core.BooleanVar;
import org.jacop.core.Store;
import org.jacop.jasat.utils.structures.IntVec;
import org.jacop.satwrapper.SatWrapper;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.Search;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.search.SmallestDomain;

public class SATParking3 {
public static void main(String[] args) {

        String filename = args[0];
        String line = null;
        int lane_number;
        int locations;
        int j = 0;

        try {
                FileReader filereader = new FileReader (filename);
                BufferedReader bufferedreader = new BufferedReader (filereader);

                line = bufferedreader.readLine();
                String data[] = line.split(" ");
                lane_number = Integer.parseInt(data[0]);
                locations = Integer.parseInt(data[1]);

                String parking[][] = new String [lane_number][locations];

                while((line = bufferedreader.readLine()) != null) {
                        String car_info[] = line.split(" ");
                        for (int i = 0; i < locations; i++) {
                                parking[j][i] = car_info[i];
                        }
                        j++;
                        System.out.println(line);
                }

                bufferedreader.close();

                //Times
                String category[][] = new String [lane_number][locations];
                for(int i = 0; i < lane_number; i++){
                  for(int k = 0; k < locations; k++){
                    category[i][k] = String.valueOf(parking[i][k].charAt(0));
                  }
                }

                String arrival[][] = new String [lane_number][locations];
                for(int i = 0; i < lane_number; i++){
                  for(int k = 0; k < locations; k++){
		    arrival[i][k] = String.valueOf(parking[i][k].charAt(1));
                  }
                }

                //SAT
                Store store = new Store();
                SatWrapper satWrapper = new SatWrapper();
                store.impose(satWrapper);

                BooleanVar[][] a = new BooleanVar[lane_number][locations];
                BooleanVar[][] b = new BooleanVar[lane_number][locations];
                BooleanVar[][] c = new BooleanVar[lane_number][locations];
                BooleanVar[][] empty = new BooleanVar[lane_number][locations];
		int literalA[][] = new int[lane_number][locations];
		int literalB[][] = new int[lane_number][locations];
		int literalC[][] = new int[lane_number][locations];
		int literalEmpty[][] = new int[lane_number][locations];

		for (int i = 0; i<lane_number; i++) {
			for (int k = 0; k<locations; k++) {
				a[i][k] = new BooleanVar(store, "SPOT: [" +i+ ","+k+ "] has category A");
				b[i][k] = new BooleanVar(store, "SPOT: [" +i+ ","+k+ "] has category B");
				c[i][k] = new BooleanVar(store, "SPOT: [" +i+ ","+k+ "] has category C");
				empty[i][k] = new BooleanVar(store, "SPOT: [" +i+ ","+k+ "] is empty");
		            	satWrapper.register(a[i][k]);
		            	satWrapper.register(b[i][k]);
		            	satWrapper.register(c[i][k]);
		            	satWrapper.register(empty[i][k]);

				switch(category[i][k]){
					case "A":
						literalA[i][k] = satWrapper.cpVarToBoolVar(a[i][k], 1, true);	
						literalB[i][k] = satWrapper.cpVarToBoolVar(b[i][k], 1, true);
						literalC[i][k] = satWrapper.cpVarToBoolVar(c[i][k], 1, true);
						literalEmpty[i][k] = satWrapper.cpVarToBoolVar(empty[i][k], 1, true);

						addClause(satWrapper,literalA[i][k],-literalB[i][k],-literalC[i][k],-literalEmpty[i][k]);

						if(k > 0 && k < locations-1){
							if(!parking[i][k+1].equals("__") && !parking[i][k-1].equals("__")){
								if(category[i][k].charAt(0) > category[i][k+1].charAt(0) || category[i][k].charAt(0) > category[i][k-1].charAt(0)){
									literalA[i][k+1] = satWrapper.cpVarToBoolVar(a[i][k+1], 1, true);
									literalEmpty[i][k+1] = satWrapper.cpVarToBoolVar(a[i][k+1], 1, true);
									literalA[i][k-1] = satWrapper.cpVarToBoolVar(a[i][k-1], 1, true);
									literalEmpty[i][k-1] = satWrapper.cpVarToBoolVar(a[i][k-1], 1, true);
									addClause(satWrapper,literalA[i][k+1],literalEmpty[i][k+1]);	
									addClause(satWrapper,literalA[i][k-1],literalEmpty[i][k-1]);			
								}

								if(category[i][k+1].equals("A") && category[i][k-1].equals("A")){
									if(Integer.parseInt(arrival[i][k]) > Integer.parseInt(arrival[i][k+1]) || Integer.parseInt(arrival[i][k]) > Integer.parseInt(arrival[i][k-1])){
										literalA[i][k+1] = satWrapper.cpVarToBoolVar(a[i][k+1], 1, true);
										literalB[i][k+1] = satWrapper.cpVarToBoolVar(b[i][k+1], 1, true);
										literalC[i][k+1] = satWrapper.cpVarToBoolVar(c[i][k+1], 1, true);
										literalEmpty[i][k+1] = satWrapper.cpVarToBoolVar(a[i][k+1], 1, true);
										literalA[i][k-1] = satWrapper.cpVarToBoolVar(a[i][k-1], 1, true);
										literalB[i][k-1] = satWrapper.cpVarToBoolVar(b[i][k-1], 1, true);
										literalC[i][k-1] = satWrapper.cpVarToBoolVar(c[i][k-1], 1, true);
										literalEmpty[i][k-1] = satWrapper.cpVarToBoolVar(a[i][k-1], 1, true);
										addClause(satWrapper,literalA[i][k+1],-literalB[i][k+1],-literalC[i][k+1],literalEmpty[i][k+1]);	
										addClause(satWrapper,literalA[i][k-1],-literalB[i][k-1],-literalC[i][k-1],literalEmpty[i][k-1]);	
									}
									else{
										literalA[i][k+1] = satWrapper.cpVarToBoolVar(a[i][k+1], 1, true);
										literalB[i][k+1] = satWrapper.cpVarToBoolVar(b[i][k+1], 1, true);
										literalC[i][k+1] = satWrapper.cpVarToBoolVar(c[i][k+1], 1, true);
										literalEmpty[i][k+1] = satWrapper.cpVarToBoolVar(a[i][k+1], 1, true);
										literalA[i][k-1] = satWrapper.cpVarToBoolVar(a[i][k-1], 1, true);
										literalB[i][k-1] = satWrapper.cpVarToBoolVar(b[i][k-1], 1, true);
										literalC[i][k-1] = satWrapper.cpVarToBoolVar(c[i][k-1], 1, true);
										literalEmpty[i][k-1] = satWrapper.cpVarToBoolVar(a[i][k-1], 1, true);
										addClause(satWrapper,literalA[i][k+1],-literalB[i][k+1],-literalC[i][k+1],-literalEmpty[i][k+1]);	
										addClause(satWrapper,literalA[i][k-1],-literalB[i][k-1],-literalC[i][k-1],-literalEmpty[i][k-1]);	
									}													
								}
							}
							else{
								addClause(satWrapper,literalEmpty[i][k+1]);	
								addClause(satWrapper,literalEmpty[i][k-1]);
								break;
							}
						}
						else{
							addClause(satWrapper,-literalEmpty[i][k]);
						}
					break;
					
					case "B":
						literalA[i][k] = satWrapper.cpVarToBoolVar(a[i][k], 1, true);	
						literalB[i][k] = satWrapper.cpVarToBoolVar(b[i][k], 1, true);
						literalC[i][k] = satWrapper.cpVarToBoolVar(c[i][k], 1, true);
						literalEmpty[i][k] = satWrapper.cpVarToBoolVar(empty[i][k], 1, true);

						addClause(satWrapper,-literalA[i][k],literalB[i][k],-literalC[i][k],-literalEmpty[i][k]);

						if(k > 0 && k < locations-1){
							if(!parking[i][k+1].equals("__") && !parking[i][k-1].equals("__")){
								if(category[i][k].charAt(0) > category[i][k+1].charAt(0) || category[i][k].charAt(0) > category[i][k-1].charAt(0)){
									literalB[i][k+1] = satWrapper.cpVarToBoolVar(b[i][k+1], 1, true);
									literalEmpty[i][k+1] = satWrapper.cpVarToBoolVar(a[i][k+1], 1, true);
									literalB[i][k-1] = satWrapper.cpVarToBoolVar(b[i][k-1], 1, true);
									literalEmpty[i][k-1] = satWrapper.cpVarToBoolVar(a[i][k-1], 1, true);
									addClause(satWrapper,literalB[i][k+1],literalEmpty[i][k+1]);	
									addClause(satWrapper,literalB[i][k-1],literalEmpty[i][k-1]);			
								}

								if(category[i][k+1].equals("B") && category[i][k-1].equals("B")){
									if(Integer.parseInt(arrival[i][k]) > Integer.parseInt(arrival[i][k+1]) || Integer.parseInt(arrival[i][k]) > Integer.parseInt(arrival[i][k-1])){
										literalA[i][k+1] = satWrapper.cpVarToBoolVar(a[i][k+1], 1, true);
										literalB[i][k+1] = satWrapper.cpVarToBoolVar(b[i][k+1], 1, true);
										literalC[i][k+1] = satWrapper.cpVarToBoolVar(c[i][k+1], 1, true);
										literalEmpty[i][k+1] = satWrapper.cpVarToBoolVar(a[i][k+1], 1, true);
										literalA[i][k-1] = satWrapper.cpVarToBoolVar(a[i][k-1], 1, true);
										literalB[i][k-1] = satWrapper.cpVarToBoolVar(b[i][k-1], 1, true);
										literalC[i][k-1] = satWrapper.cpVarToBoolVar(c[i][k-1], 1, true);
										literalEmpty[i][k-1] = satWrapper.cpVarToBoolVar(a[i][k-1], 1, true);
										addClause(satWrapper,-literalA[i][k+1],literalB[i][k+1],-literalC[i][k+1],literalEmpty[i][k+1]);	
										addClause(satWrapper,-literalA[i][k-1],literalB[i][k-1],-literalC[i][k-1],literalEmpty[i][k-1]);	
									}
									else{
										literalA[i][k+1] = satWrapper.cpVarToBoolVar(a[i][k+1], 1, true);
										literalB[i][k+1] = satWrapper.cpVarToBoolVar(b[i][k+1], 1, true);
										literalC[i][k+1] = satWrapper.cpVarToBoolVar(c[i][k+1], 1, true);
										literalEmpty[i][k+1] = satWrapper.cpVarToBoolVar(a[i][k+1], 1, true);
										literalA[i][k-1] = satWrapper.cpVarToBoolVar(a[i][k-1], 1, true);
										literalB[i][k-1] = satWrapper.cpVarToBoolVar(b[i][k-1], 1, true);
										literalC[i][k-1] = satWrapper.cpVarToBoolVar(c[i][k-1], 1, true);
										literalEmpty[i][k-1] = satWrapper.cpVarToBoolVar(a[i][k-1], 1, true);
										addClause(satWrapper,-literalA[i][k+1],literalB[i][k+1],-literalC[i][k+1],-literalEmpty[i][k+1]);	
										addClause(satWrapper,-literalA[i][k-1],literalB[i][k-1],-literalC[i][k-1],-literalEmpty[i][k-1]);	
									}													
								}
							}
							else{
								addClause(satWrapper,literalEmpty[i][k+1]);	
								addClause(satWrapper,literalEmpty[i][k-1]);
								break;
							}
						}
						else{
							addClause(satWrapper,-literalEmpty[i][k]);
						}
					break;
					
					case "C":
						literalA[i][k] = satWrapper.cpVarToBoolVar(a[i][k], 1, true);	
						literalB[i][k] = satWrapper.cpVarToBoolVar(b[i][k], 1, true);
						literalC[i][k] = satWrapper.cpVarToBoolVar(c[i][k], 1, true);
						literalEmpty[i][k] = satWrapper.cpVarToBoolVar(empty[i][k], 1, true);

						addClause(satWrapper,-literalA[i][k],-literalB[i][k],literalC[i][k],-literalEmpty[i][k]);

						if(k > 0 && k < locations-1){
							if(!parking[i][k+1].equals("__") && !parking[i][k-1].equals("__")){
								if(category[i][k].charAt(0) > category[i][k+1].charAt(0) || category[i][k].charAt(0) > category[i][k-1].charAt(0)){
									literalC[i][k+1] = satWrapper.cpVarToBoolVar(c[i][k+1], 1, true);
									literalEmpty[i][k+1] = satWrapper.cpVarToBoolVar(a[i][k+1], 1, true);
									literalC[i][k-1] = satWrapper.cpVarToBoolVar(c[i][k-1], 1, true);
									literalEmpty[i][k-1] = satWrapper.cpVarToBoolVar(a[i][k-1], 1, true);
									addClause(satWrapper,literalC[i][k+1],literalEmpty[i][k+1]);	
									addClause(satWrapper,literalC[i][k-1],literalEmpty[i][k-1]);			
								}

								if(category[i][k+1].equals("B") && category[i][k-1].equals("B")){
									if(Integer.parseInt(arrival[i][k]) > Integer.parseInt(arrival[i][k+1]) || Integer.parseInt(arrival[i][k]) > Integer.parseInt(arrival[i][k-1])){
										literalA[i][k+1] = satWrapper.cpVarToBoolVar(a[i][k+1], 1, true);
										literalB[i][k+1] = satWrapper.cpVarToBoolVar(b[i][k+1], 1, true);
										literalC[i][k+1] = satWrapper.cpVarToBoolVar(c[i][k+1], 1, true);
										literalEmpty[i][k+1] = satWrapper.cpVarToBoolVar(a[i][k+1], 1, true);
										literalA[i][k-1] = satWrapper.cpVarToBoolVar(a[i][k-1], 1, true);
										literalB[i][k-1] = satWrapper.cpVarToBoolVar(b[i][k-1], 1, true);
										literalC[i][k-1] = satWrapper.cpVarToBoolVar(c[i][k-1], 1, true);
										literalEmpty[i][k-1] = satWrapper.cpVarToBoolVar(a[i][k-1], 1, true);
										addClause(satWrapper,-literalA[i][k+1],literalB[i][k+1],-literalC[i][k+1],literalEmpty[i][k+1]);	
										addClause(satWrapper,-literalA[i][k-1],literalB[i][k-1],-literalC[i][k-1],literalEmpty[i][k-1]);	
									}
									else{
										literalA[i][k+1] = satWrapper.cpVarToBoolVar(a[i][k+1], 1, true);
										literalB[i][k+1] = satWrapper.cpVarToBoolVar(b[i][k+1], 1, true);
										literalC[i][k+1] = satWrapper.cpVarToBoolVar(c[i][k+1], 1, true);
										literalEmpty[i][k+1] = satWrapper.cpVarToBoolVar(a[i][k+1], 1, true);
										literalA[i][k-1] = satWrapper.cpVarToBoolVar(a[i][k-1], 1, true);
										literalB[i][k-1] = satWrapper.cpVarToBoolVar(b[i][k-1], 1, true);
										literalC[i][k-1] = satWrapper.cpVarToBoolVar(c[i][k-1], 1, true);
										literalEmpty[i][k-1] = satWrapper.cpVarToBoolVar(a[i][k-1], 1, true);
										addClause(satWrapper,-literalA[i][k+1],literalB[i][k+1],-literalC[i][k+1],-literalEmpty[i][k+1]);	
										addClause(satWrapper,-literalA[i][k-1],literalB[i][k-1],-literalC[i][k-1],-literalEmpty[i][k-1]);	
									}													
								}
							}
							else{
								addClause(satWrapper,literalEmpty[i][k+1]);	
								addClause(satWrapper,literalEmpty[i][k-1]);
								break;
							}
						}
						else{
							addClause(satWrapper,-literalEmpty[i][k]);
						}
					break;
		
					default: break;			
				}
			}
		}

		BooleanVar[] allVariables = new BooleanVar[lane_number*locations*4];
		int count = 0;

		for (int i = 0; i<lane_number; i++) {
                  	for (int k = 0; k<locations; k++) {
				allVariables[count] = a[i][k];
				count++;
			}
		}
		for (int i = 0; i<lane_number; i++) {
                  	for (int k = 0; k<locations; k++) {
				allVariables[count] = b[i][k];
				count++;
			}
		}
		for (int i = 0; i<lane_number; i++) {
                  	for (int k = 0; k<locations; k++) {
				allVariables[count] = c[i][k];
				count++;
			}
		}
		for (int i = 0; i<lane_number; i++) {
                  	for (int k = 0; k<locations; k++) {
				allVariables[count] = empty[i][k];
				count++;
			}
		}

      		//Solve
                Search<BooleanVar> search = new DepthFirstSearch<BooleanVar>();
                SelectChoicePoint<BooleanVar> select = new SimpleSelect<BooleanVar>(allVariables,
                         new SmallestDomain<BooleanVar>(), new IndomainMin<BooleanVar>());
                Boolean result = search.labeling(store, select);

		if(result) System.out.println("Satisfiable");
		else{System.out.println("Not satisfiable");}


        } //Try

        catch(IOException ex) {
                System.out.println("Error reading file '" + filename + "'");
        }
        
        

      }

		public static void addClause(SatWrapper satWrapper, int literal1){
			IntVec clause = new IntVec(satWrapper.pool);
			clause.add(literal1);
			satWrapper.addModelClause(clause.toArray());
		}
		public static void addClause(SatWrapper satWrapper, int literal1, int literal2){
			IntVec clause = new IntVec(satWrapper.pool);
			clause.add(literal1);
			clause.add(literal2);
			satWrapper.addModelClause(clause.toArray());
		}
		public static void addClause(SatWrapper satWrapper, int literal1, int literal2, int literal3, int literal4){
			IntVec clause = new IntVec(satWrapper.pool);
			clause.add(literal1);
			clause.add(literal2);
			clause.add(literal3);
			clause.add(literal4);
			satWrapper.addModelClause(clause.toArray());
		}
}

