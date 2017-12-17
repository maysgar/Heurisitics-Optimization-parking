import java.io.BufferedReader;
import java.io.FileReader;
import java.io.File;
import java.io.IOException;
import java.io.PrintWriter;
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

public class SATParkingV5 {
public static void main(String[] args) {

        String filename = args[0];
        String line = null;
        int N = 0;
        int L = 0;
        int j = 0;
        String parking[][] = null;
        String category[][] = null;
        float wTime[][] = null;
        String arrival[][] = null;

        try {
          FileReader filereader = new FileReader (filename);
          BufferedReader bufferedreader = new BufferedReader (filereader);

          line = bufferedreader.readLine();
          String data[] = line.split(" ");
          N = Integer.parseInt(data[0]);
          L = Integer.parseInt(data[1]);
          parking = new String[N][L];
          category = new String[N][L];
          wTime = new float[N][L];
          arrival = new String[N][L];

          while((line = bufferedreader.readLine()) != null) {
            String car_info[] = line.split(" ");
            for (int i=0; i<L; i++) parking[j][i] = car_info[i];
            j++;
            System.out.println(line);
          }
          bufferedreader.close();

          //Times
          for(int i=0; i<N; i++) for(int k=0; k<L; k++){
              category[i][k] = String.valueOf(parking[i][k].charAt(0));
              switch(category[i][k]){
                case "A":
                  wTime[i][k] = 0.5f;
                break;
                case "B":
                  wTime[i][k] = 2f;
                break;
                case "C":
                  wTime[i][k] = 3f;
                break;
                default:
                  wTime[i][k] = 0f;
                break;
              }
          }

          for(int i=0; i<N; i++) for(int k=0; k<L; k++){
    				if(parking[i][k].equals("__")) arrival[i][k] = String.valueOf(0);
    				else arrival[i][k] = String.valueOf(parking[i][k].charAt(1));
          }
        }
        catch(IOException ex) {
            System.out.println("Error reading file '" + filename + "'");
        }

        //SAT
        Store store = new Store();
        SatWrapper satWrapper = new SatWrapper();
        store.impose(satWrapper);

        //Boolean variales creation
        //car has entered after next one
        BooleanVar [][] afterNext = new BooleanVar[N][L];
        //car has entered after behind one
        BooleanVar [][] afterBehind = new BooleanVar[N][L];
        //car has same category as next one
        BooleanVar [][] sameCategoryNext = new BooleanVar[N][L];
        //car has same category as behind one
        BooleanVar [][] sameCategoryBehind = new BooleanVar[N][L];
        //car has higher waiting time than the next one
        BooleanVar [][] lowCatNext = new BooleanVar[N][L];
        //car has higher waiting time than the behind one
        BooleanVar [][] lowCatBehind = new BooleanVar[N][L];
        //there is no car
        BooleanVar [][] empty = new BooleanVar[N][L];
        //car is on the edge of the parking
        BooleanVar [][] edge = new BooleanVar[N][L];

        int[][] literalAfterNext = new int[N][L];
        int[][] literalAfterBehind = new int[N][L];
        int[][] literalSameCategoryNext = new int[N][L];
        int[][] literalSameCategoryBehind = new int[N][L];
        int[][] literalLowCatNext = new int[N][L];
        int[][] literalLowCatBehind = new int[N][L];
        int[][] literalEmpty = new int[N][L];
        int[][] literalEdge = new int[N][L];

        //Set up
        for (int i=0; i<N; i++) for (int k=0; k<L; k++){
          afterNext[i][k] = new BooleanVar(store,"Pos ["+i+","+k+"]: has entered after the next one");
          afterBehind[i][k] = new BooleanVar(store,"Pos ["+i+","+k+"]: has entered after the behind one");
          sameCategoryNext[i][k] = new BooleanVar(store,"Pos ["+i+","+k+"]: has same category as the next one");
          sameCategoryBehind[i][k] = new BooleanVar(store,"Pos ["+i+","+k+"]: has same category as the behind one");
          lowCatNext[i][k] = new BooleanVar(store,"Pos ["+i+","+k+"]: has higher waiting time than the next one");
          lowCatBehind[i][k] = new BooleanVar(store,"Pos ["+i+","+k+"]:has higher waiting time than the behind one");
          empty[i][k] = new BooleanVar(store,"Pos ["+i+","+k+"]: is empty");
          edge[i][k] = new BooleanVar(store,"Pos ["+i+","+k+"]: is on the edge");
          satWrapper.register(afterNext[i][k]);
          satWrapper.register(afterBehind[i][k]);
          satWrapper.register(sameCategoryNext[i][k]);
          satWrapper.register(sameCategoryBehind[i][k]);
          satWrapper.register(lowCatNext[i][k]);
          satWrapper.register(lowCatBehind[i][k]);
          satWrapper.register(empty[i][k]);
          satWrapper.register(edge[i][k]);
          literalAfterNext[i][k] = satWrapper.cpVarToBoolVar(afterNext[i][k], 1, true);
          literalAfterBehind[i][k] = satWrapper.cpVarToBoolVar(afterBehind[i][k], 1, true);
          literalSameCategoryNext[i][k] = satWrapper.cpVarToBoolVar(sameCategoryNext[i][k], 1, true);
          literalSameCategoryBehind[i][k] = satWrapper.cpVarToBoolVar(sameCategoryBehind[i][k], 1, true);
          literalLowCatNext[i][k] = satWrapper.cpVarToBoolVar(lowCatNext[i][k], 1, true);
          literalLowCatBehind[i][k] = satWrapper.cpVarToBoolVar(lowCatBehind[i][k], 1, true);
          literalEmpty[i][k] = satWrapper.cpVarToBoolVar(empty[i][k], 1, true);
          literalEdge[i][k] = satWrapper.cpVarToBoolVar(edge[i][k], 1, true);
        }

        //This loop will only go through the inside of the parkingOut
        //  leaving the k=0 and k=L-1 columns with no visits
        for (int i=0; i<N; i++) for (int k=0; k<L; k++){
          //If spot is empty...
          if(parking[i][k].equals("__")) addClause(satWrapper,literalEmpty[i][k]);
          //If spots contain a car...
          else{
            //If the spot is on the edge of the parking...
            addClause(satWrapper,-literalEmpty[i][k]);
            if(k == 0 || k == L-1) addClause(satWrapper,literalEdge[i][k]);
            //If the spot is on other places...
            else{
              addClause(satWrapper,-literalEdge[i][k]);
              if(!category[i][k+1].equals("_")){
                //Checking next spot
                if(category[i][k].equals(category[i][k+1])){
                  addClause(satWrapper,literalSameCategoryNext[i][k]);
                  addClause(satWrapper,-literalLowCatNext[i][k]);
                }
                else{
                  addClause(satWrapper,-literalSameCategoryNext[i][k]);
                  if(wTime[i][k] > wTime[i][k+1]){
                    addClause(satWrapper,literalLowCatNext[i][k]);
                  }
                  else{
                    addClause(satWrapper,-literalLowCatNext[i][k]);
                  }
                }
                if(Integer.parseInt(arrival[i][k]) > Integer.parseInt(arrival[i][k+1])){
                  addClause(satWrapper,literalAfterNext[i][k]);
                }
                else{
                  addClause(satWrapper,-literalAfterNext[i][k]);
                }
              }
              else{
                addClause(satWrapper,literalLowCatNext[i][k]);
        				addClause(satWrapper,literalSameCategoryNext[i][k]);
        				addClause(satWrapper,literalAfterNext[i][k]);
              }
              if(!category[i][k-1].equals("_")){
                //Checking the spot behind
                if(category[i][k].equals(category[i][k-1])){
                  addClause(satWrapper,literalSameCategoryBehind[i][k]);
                  addClause(satWrapper,-literalLowCatBehind[i][k]);
                }
                else{
                  addClause(satWrapper,-literalSameCategoryBehind[i][k]);
                  if(wTime[i][k] > wTime[i][k-1]){
                    addClause(satWrapper,literalLowCatBehind[i][k]);
                  }
                  else{
                    addClause(satWrapper,-literalLowCatBehind[i][k]);
                  }
                }
                if(Integer.parseInt(arrival[i][k]) > Integer.parseInt(arrival[i][k-1])){
                  addClause(satWrapper,literalAfterBehind[i][k]);
                }
                else{
                  addClause(satWrapper,-literalAfterBehind[i][k]);
                }
              }
              else{
                addClause(satWrapper,literalLowCatBehind[i][k]);
        				addClause(satWrapper,literalSameCategoryBehind[i][k]);
        				addClause(satWrapper,literalAfterBehind[i][k]);
              }
            }
          }
        }

        // Add all clauses
        for (int i=0; i<N; i++) for (int k=0; k<L-1; k++){
          addClause(satWrapper,literalEmpty[i][k],literalEdge[i][k],literalLowCatNext[i][k],literalLowCatBehind[i][k],literalSameCategoryBehind[i][k],literalSameCategoryNext[i][k]);
          addClause(satWrapper,literalEmpty[i][k],literalEdge[i][k],literalLowCatNext[i][k],literalLowCatBehind[i][k],literalSameCategoryBehind[i][k],literalAfterNext[i][k]);
          addClause(satWrapper,literalEmpty[i][k],literalEdge[i][k],literalLowCatNext[i][k],literalLowCatBehind[i][k],literalSameCategoryNext[i][k],literalAfterBehind[i][k]);
          addClause(satWrapper,literalEmpty[i][k],literalEdge[i][k],literalLowCatNext[i][k],literalLowCatBehind[i][k],literalAfterBehind[i][k],literalAfterNext[i][k]);
        }

        BooleanVar[] allVariables = new BooleanVar[N*L*8]; int count = 0;
        for(int i=0; i<N; i++) for(int k=0; k<L; k++,count++) allVariables[count] = afterNext[i][k];
        for(int i=0; i<N; i++) for(int k=0; k<L; k++,count++) allVariables[count] = afterBehind[i][k];
        for(int i=0; i<N; i++) for(int k=0; k<L; k++,count++) allVariables[count] = sameCategoryNext[i][k];
        for(int i=0; i<N; i++) for(int k=0; k<L; k++,count++) allVariables[count] = sameCategoryBehind[i][k];
        for(int i=0; i<N; i++) for(int k=0; k<L; k++,count++) allVariables[count] = lowCatNext[i][k];
        for(int i=0; i<N; i++) for(int k=0; k<L; k++,count++) allVariables[count] = lowCatBehind[i][k];
        for(int i=0; i<N; i++) for(int k=0; k<L; k++,count++) allVariables[count] = empty[i][k];
        for(int i=0; i<N; i++) for(int k=0; k<L; k++,count++) allVariables[count] = edge[i][k];

        // Solve the problem
        Search<BooleanVar> search = new DepthFirstSearch<BooleanVar>();
        SelectChoicePoint<BooleanVar> select = new SimpleSelect<BooleanVar>(allVariables, new SmallestDomain<BooleanVar>(), new IndomainMin<BooleanVar>());
        Boolean result = search.labeling(store, select);

        boolean[][] blocked = new boolean[N][L];
				//Right position that sets in between position free == 0; Left position == 1
				boolean[][][] pos = new boolean[N][L][2];

				//Loop checking if car is blocked by brute force conditions to set up a boolean var
				for(int i=0; i<N; i++) for(int k=1; k<L-1; k++){
					switch(category[i][k]){
						case "A":
							if(category[i][k+1].equals("_") || (category[i][k+1].charAt(0) < category[i][k].charAt(0)) ||
              (category[i][k+1].equals("A") && (Integer.parseInt(arrival[i][k+1]) < Integer.parseInt(arrival[i][k])))){
								blocked[i][k] = false;
								pos[i][k][0] = true;
							}
							if(category[i][k-1].equals("_") || (category[i][k-1].charAt(0) < category[i][k].charAt(0)) ||
              (category[i][k-1].equals("A") && (Integer.parseInt(arrival[i][k-1]) < Integer.parseInt(arrival[i][k])))) {
								blocked[i][k] = false;
								pos[i][k][1] = true;
							}
							else{
								blocked[i][k] = true;
							}
						break;

						case "B":
							if(category[i][k+1].equals("_") || (category[i][k+1].charAt(0) < category[i][k].charAt(0)) ||
              (category[i][k+1].equals("B") && (Integer.parseInt(arrival[i][k+1]) < Integer.parseInt(arrival[i][k])))){
								blocked[i][k] = false;
								pos[i][k][0] = true;
							}
							if(category[i][k-1].equals("_") || (category[i][k-1].charAt(0) < category[i][k].charAt(0)) ||
              (category[i][k-1].equals("B") && (Integer.parseInt(arrival[i][k-1]) < Integer.parseInt(arrival[i][k])))) {
								blocked[i][k] = false;
								pos[i][k][1] = true;
							}
							else{
								blocked[i][k] = true;
							}
						break;

						case "C":
							if(category[i][k+1].equals("_") || (category[i][k+1].charAt(0) < category[i][k].charAt(0)) ||
              (category[i][k+1].equals("C") && (Integer.parseInt(arrival[i][k+1]) < Integer.parseInt(arrival[i][k])))){
								blocked[i][k] = false;
								pos[i][k][0] = true;
							}
							if(category[i][k-1].equals("_") || (category[i][k-1].charAt(0) < category[i][k].charAt(0)) ||
              (category[i][k-1].equals("C") && (Integer.parseInt(arrival[i][k-1]) < Integer.parseInt(arrival[i][k])))) {
								blocked[i][k] = false;
								pos[i][k][1] = true;
							}
							else{
								blocked[i][k] = true;
							}
					}
				}

        String[] move = new String[]{">>","<<"};
        String[][] parkingOut = new String[N][L];
        String newFile = "";
        PrintWriter writer = null;

				//If result is true -> car is not blocked
				if(result){
          //Take name of the inputfile
          for (int i=0; i<filename.length(); i++) {
            if(filename.charAt(i) == '.'){
              newFile = filename.substring(0,i);
              break;
            }
          }

					try{writer = new PrintWriter(newFile+".output","UTF-8");}
          catch(IOException ex) {
              System.out.println("Error creating '" + filename + "'");
          }
					for(int i = 0; i<N; i++) for(int k = 0; k<L; k++){
							if(parking[i][k].equals("__")){
								writer.println("__ ");
							}
							else if(k == 0){
								//Move to the left if its in the far left column
                parkingOut[i][k] = move[1];
								writer.println(parkingOut[i][k]+" ");
							}
							else if(k == (L-1)){
								//Move to the right if its in the far right column
                parkingOut[i][k] = move[0];
								writer.println(parkingOut[i][k]+" ");
							}
							else if(!blocked[i][k] && pos[i][k][0]){
								//Move right
                parkingOut[i][k] = move[0];
								writer.println(parkingOut[i][k]+" ");
							}
							else if(!blocked[i][k] && pos[i][k][1]){
								//Move left
                parkingOut[i][k] = move[1];
								writer.println(parkingOut[i][k]+" ");
							}
							else continue;
							if(k==(L-1)) writer.println("\n");
						}
          writer.close();
				}
				else System.out.println("Unsatisfiable: One or More Cars Are Blocked");

      }
      public static void addClause(SatWrapper satWrapper, int literal1){
        IntVec clause = new IntVec(satWrapper.pool);
        clause.add(literal1);
        satWrapper.addModelClause(clause.toArray());
      }

      public static void addClause (SatWrapper satWrapper, int literal1, int literal2, int literal3, int literal4, int literal5, int literal6) {
        IntVec clause = new IntVec(satWrapper.pool);
        clause.add(literal1);
        clause.add(literal2);
        clause.add(literal3);
        clause.add(literal4);
        clause.add(literal5);
        clause.add(literal6);
        satWrapper.addModelClause(clause.toArray());
      }
    }
