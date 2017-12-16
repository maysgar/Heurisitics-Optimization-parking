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

public class SATParking {
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
				if(parking[i][k].equals("__")){
				arrival[i][k] = String.valueOf(0);
				}
				else{
				arrival[i][k] = String.valueOf(parking[i][k].charAt(1));
				}
                  }
                }

                //SAT
                Store store = new Store();
                SatWrapper satWrapper = new SatWrapper();
                store.impose(satWrapper);

				// True if current car has arrived after the front one
                BooleanVar[][] timeFront = new BooleanVar[lane_number][locations];
				// True if current car has arrived after the one behind
                BooleanVar[][] timeBehind = new BooleanVar[lane_number][locations];
				// True if current car has a bigger category than the front one
                BooleanVar[][] carFrontCat = new BooleanVar[lane_number][locations];
				// True if current car has a bigger category than the one behind
				BooleanVar[][] carBehindCat = new BooleanVar[lane_number][locations];
				// True if current car has the same category as the front one
                BooleanVar[][] sameFrontCat = new BooleanVar[lane_number][locations];
				// True if current car has the same category as the one behind
                BooleanVar[][] sameBehindCat = new BooleanVar[lane_number][locations];
                int[][] literalTimeFront = new int[lane_number][locations];
                int[][] literalTimeBehind = new int[lane_number][locations];
                int[][] literalCarFrontCat = new int[lane_number][locations];
                int[][] literalCarBehindCat = new int[lane_number][locations];
				int[][] literalSameFrontCat = new int[lane_number][locations];
                int[][] literalSameBehindCat = new int[lane_number][locations];

				// Traverse the whole map, through lanes and locations on each lane
                for (int i = 0; i<lane_number; i++) {
					for (int k = 0; k<locations; k++) {

						timeFront[i][k] = new BooleanVar(store, "Time of arrival of car: [" +i+ ","+k+ "] greater than the front one");
						timeBehind[i][k] = new BooleanVar(store, "Time of arrival of car: [" +i+ ","+k+ "] greater than the behind one");
						carFrontCat[i][k] = new BooleanVar(store, "Category of front car is higher than the category of car: [" +i+ ","+k+ "]");
						carBehindCat[i][k] = new BooleanVar(store, "Category of the car behind is higher than the category of car: [" +i+ ","+k+ "]");
						sameFrontCat[i][k] = new BooleanVar(store, "Category is the same for car in front of car: [" +i+ ","+k+ "]");
						sameBehindCat[i][k] = new BooleanVar(store, "Category is the same for car behind of car: [" +i+ ","+k+ "]");
						satWrapper.register(sameFrontCat[i][k]);
						satWrapper.register(sameBehindCat[i][k]);
						satWrapper.register(timeFront[i][k]);
						satWrapper.register(timeBehind[i][k]);
						satWrapper.register(carFrontCat[i][k]);
						satWrapper.register(carBehindCat[i][k]);

						// If we are not in the last position of a lane
						if(k < (locations-1)){
							// If the current position has a higher time than the front one and we are sure there is a car there we set the literal to 1
              // OR if they both have the same time, we set the literal to 1, but the program will not check this case so it does not matter
							if(Integer.parseInt(arrival[i][k]) > Integer.parseInt(arrival[i][k+1]) || Integer.parseInt(arrival[i][k]) == Integer.parseInt(arrival[i][k+1])){
								// We set the literal to true (current car arrived later)
								literalTimeFront[i][k] = satWrapper.cpVarToBoolVar(timeFront[i][k], 1, true);
								addClause(satWrapper,literalTimeFront[i][k]);
							}
							// If the current position has a lower time than the front one we set the literal to 1
							if(Integer.parseInt(arrival[i][k]) < Integer.parseInt(arrival[i][k+1])) {
								literalTimeFront[i][k] = satWrapper.cpVarToBoolVar(timeFront[i][k], 1, true);
								addClause(satWrapper,-literalTimeFront[i][k]);
							}

							// If the current car category is higher than the front one AND we know there is a car there
							// OR there is no car in the current position
							// OR the current car has the same category as the front one
							if(((category[i][k].charAt(0) > category[i][k+1].charAt(0)) && !parking[i][k+1].equals("__")) || parking[i][k].equals("__") || category[i][k].equals(category[i][k+1])){
								// We set the literal to 0
								literalCarFrontCat[i][k] = satWrapper.cpVarToBoolVar(carFrontCat[i][k], 1, true);
								addClause(satWrapper,-literalCarFrontCat[i][k]);
							}
							// In the rest if the cases the literal is set to 1
							else{
								literalCarFrontCat[i][k] = satWrapper.cpVarToBoolVar(carFrontCat[i][k], 1, true);
								addClause(satWrapper,literalCarFrontCat[i][k]);
							}
							// If the car in current position has the same category as the front one AND we know there is a car there, we set the literal to 1
							if(category[i][k].equals(category[i][k+1]) && !parking[i][k+1].equals("__")){
								literalSameFrontCat[i][k] = satWrapper.cpVarToBoolVar(sameFrontCat[i][k], 1, true);
								addClause(satWrapper,literalSameFrontCat[i][k]);
							}
							// In the rest of the cases we set the literal to 0
							else{
								literalSameFrontCat[i][k] = satWrapper.cpVarToBoolVar(sameFrontCat[i][k], 1, true);
								addClause(satWrapper,-literalSameFrontCat[i][k]);
							}
						}
						// If we are not in the first position of the lane
						if(k > 0){
              // If the current position has a higher time than the front one and we are sure there is a car there we set the literal to 1
              // OR if they both have the same time, we set the literal to 1, but the program will not check this case so it does not matter
							if(Integer.parseInt(arrival[i][k]) > Integer.parseInt(arrival[i][k+1]) || Integer.parseInt(arrival[i][k]) == Integer.parseInt(arrival[i][k+1])){
								// We set the literal to true (current car arrived later)
								literalTimeBehind[i][k] = satWrapper.cpVarToBoolVar(timeBehind[i][k], 1, true);
								addClause(satWrapper,literalTimeBehind[i][k]);
							}
							// If the current position has a lower time than the front one we set the literal to 1
							if(Integer.parseInt(arrival[i][k]) < Integer.parseInt(arrival[i][k+1])) {
								literalTimeBehind[i][k] = satWrapper.cpVarToBoolVar(timeFront[i][k], 1, true);
								addClause(satWrapper,-literalTimeBehind[i][k]);
							}
							// If the current position has a bigger category than the car behind AND we are sure there is a car there
							// OR there is no car in the current position
							// OR the current car has the same category as the one behind
							if(((category[i][k].charAt(0) > category[i][k-1].charAt(0)) && !parking[i][k-1].equals("__")) || parking[i][k].equals("__") || category[i][k].equals(category[i][k-1])){
								// We set the literal to 0
								literalCarBehindCat[i][k] = satWrapper.cpVarToBoolVar(carBehindCat[i][k], 1, true);
								addClause(satWrapper,-literalCarBehindCat[i][k]);
							}
							// For the rest of the cases
							else{
								// We set the literal to 1
								literalCarBehindCat[i][k] = satWrapper.cpVarToBoolVar(carBehindCat[i][k], 1, true);
								addClause(satWrapper,literalCarBehindCat[i][k]);
							}
							// If the current category is the same as the car behind AND we are sure there is a car there
							if(category[i][k].equals(category[i][k-1]) && !parking[i][k-1].equals("__")){
								// We set the literal to 1
								literalSameBehindCat[i][k] = satWrapper.cpVarToBoolVar(sameBehindCat[i][k], 1, true);
								addClause(satWrapper,literalSameBehindCat[i][k]);
							}
							// For the rest of the cases
							else{
								// We set the literal to 0
								literalSameBehindCat[i][k] = satWrapper.cpVarToBoolVar(sameBehindCat[i][k], 1, true);
								addClause(satWrapper,-literalSameBehindCat[i][k]);
							}
						}
					}
                }

				BooleanVar[] allVariables = new BooleanVar[locations*lane_number*6];
				int count = 0;
				for(int i = 0; i<lane_number; i++){
					for(int k = 0; k<locations; k++){
						allVariables[count] = timeFront[i][k];
						count++;
					}
				}
				for(int i = 0; i<lane_number; i++){
					for(int k = 0; k<locations; k++){
						allVariables[count] = timeBehind[i][k];
						count++;
					}
				}
				for(int i = 0; i<lane_number; i++){
					for(int k = 0; k<locations; k++){
						allVariables[count] = carFrontCat[i][k];
						count++;
					}
				}
				for(int i = 0; i<lane_number; i++){
					for(int k = 0; k<locations; k++){
						allVariables[count] = carBehindCat[i][k];
						count++;
					}
				}
				for(int i = 0; i<lane_number; i++){
					for(int k = 0; k<locations; k++){
						allVariables[count] = sameFrontCat[i][k];
						count++;
					}
				}
				for(int i = 0; i<lane_number; i++){
					for(int k = 0; k<locations; k++){
						allVariables[count] = sameBehindCat[i][k];
						count++;
					}
				}

				String[] move = new String[]{"move Right","move Left"};
				boolean[][] blocked = new boolean[lane_number][locations];
				//Right position that sets in between position free == 0; Left position == 1
				boolean[][][] pos = new boolean[lane_number][locations][2];

				//Loop checking if car is blocked by brute force conditions to set up a boolean var
				for(int i = 0; i<lane_number; i++){
					for(int k = 1; k<locations-1; k++){
						switch(category[i][k]){
							case "A":
								if(category[i][k+1].equals("__") || (category[i][k+1].charAt(0) < category[i][k].charAt(0)) || (category[i][k+1].equals("A") && (Integer.parseInt(arrival[i][k+1]) < Integer.parseInt(arrival[i][k])))){
									blocked[i][k] = false;
									pos[i][k][0] = true;
								}
								else if(category[i][k-1].equals("__") || (category[i][k-1].charAt(0) < category[i][k].charAt(0)) || (category[i][k-1].equals("A") && (Integer.parseInt(arrival[i][k-1]) < Integer.parseInt(arrival[i][k])))) {
									blocked[i][k] = false;
									pos[i][k][1] = true;
								}
								else{
									blocked[i][k] = true;
								}
							break;

							case "B":
								if(category[i][k+1].equals("__") || (category[i][k+1].charAt(0) < category[i][k].charAt(0)) || (category[i][k+1].equals("B") && (Integer.parseInt(arrival[i][k+1]) < Integer.parseInt(arrival[i][k])))){
									blocked[i][k] = false;
									pos[i][k][0] = true;
								}
								else if(category[i][k-1].equals("__") || (category[i][k-1].charAt(0) < category[i][k].charAt(0)) || (category[i][k-1].equals("B") && (Integer.parseInt(arrival[i][k-1]) < Integer.parseInt(arrival[i][k])))) {
									blocked[i][k] = false;
									pos[i][k][1] = true;
								}
								else{
									blocked[i][k] = true;
								}
							break;

							case "C":
								if(category[i][k+1].equals("__") || (category[i][k+1].charAt(0) < category[i][k].charAt(0)) || (category[i][k+1].equals("C") && (Integer.parseInt(arrival[i][k+1]) < Integer.parseInt(arrival[i][k])))){
									blocked[i][k] = false;
									pos[i][k][0] = true;
								}
								else if(category[i][k-1].equals("__") || (category[i][k-1].charAt(0) < category[i][k].charAt(0)) || (category[i][k-1].equals("C") && (Integer.parseInt(arrival[i][k-1]) < Integer.parseInt(arrival[i][k])))) {
									blocked[i][k] = false;
									pos[i][k][1] = true;
								}
								else{
									blocked[i][k] = true;
								}
						}
					}
				}

				//Constraints
				for (int i = 0; i<lane_number; i++) {
					for (int k = 0; k<locations; k++) {
						addClause(satWrapper,-literalCarFrontCat[i][k],-literalCarBehindCat[i][k],literalSameFrontCat[i][k],literalSameBehindCat[i][k]);
						addClause(satWrapper,-literalCarFrontCat[i][k],-literalCarBehindCat[i][k],literalSameFrontCat[i][k],literalTimeBehind[i][k]);
						addClause(satWrapper,-literalCarFrontCat[i][k],-literalCarBehindCat[i][k],literalSameBehindCat[i][k],literalTimeFront[i][k]);
						addClause(satWrapper,-literalCarFrontCat[i][k],-literalCarBehindCat[i][k],literalSameBehindCat[i][k],literalTimeBehind[i][k]);
					}
				}

				//Solve
				Search<BooleanVar> search = new DepthFirstSearch<BooleanVar>();
				SelectChoicePoint<BooleanVar> select = new SimpleSelect<BooleanVar>(allVariables,
						 new SmallestDomain<BooleanVar>(), new IndomainMin<BooleanVar>());
				Boolean result = search.labeling(store, select);

				//If result is true -> car is not blocked
				if(result){
					//PrintWriter writer = new PrintWriter("output.txt","UTF-8");
					System.out.println("Satisfiable: No Car Blocked");
					for(int i = 0; i<lane_number; i++){
						for(int k = 0; k<locations; k++){
							if(parking[i][k].equals("__")){
								System.out.println("No car here");
							}
							else if(k == 0){
								//Move to the left if its in the far left column
								System.out.println("Car in pos: [" + i + "," + k + "] has to " + move[1]);
							}
							else if(k == (locations-1)){
								//Move to the right if its in the far right column
								System.out.println("Car in pos: [" + i + "," + k + "] has to " + move[0]);
							}
							else if(!blocked[i][k] && pos[i][k][0]){
								//Move right
								System.out.println("Car in pos: [" + i + "," + k + "] has to " + move[0]);
							}
							else if(!blocked[i][k] && pos[i][k][1]){
								//Move left
								System.out.println("Car in pos: [" + i + "," + k + "] has to " + move[1]);
							}
							else{
								continue;
							}
						}
					}
				}
				else{System.out.println("Unsatisfiable: One or More Cars Are Blocked");}


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
	public static void addClause(SatWrapper satWrapper, int literal1, int literal2, int literal3, int literal4){
		IntVec clause = new IntVec(satWrapper.pool);
		clause.add(literal1);
		clause.add(literal2);
		clause.add(literal3);
		clause.add(literal4);
		satWrapper.addModelClause(clause.toArray());
	}
}
