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

                BooleanVar[][] timeFront = new BooleanVar[lane_number][locations];
                BooleanVar[][] timeBehind = new BooleanVar[lane_number][locations];
                BooleanVar[][] carFrontCat = new BooleanVar[lane_number][locations];
		BooleanVar[][] carBehindCat = new BooleanVar[lane_number][locations];
                BooleanVar[][] sameFrontCat = new BooleanVar[lane_number][locations];
                BooleanVar[][] sameBehindCat = new BooleanVar[lane_number][locations];
                int[][] literalTimeFront = new int[lane_number][locations];
                int[][] literalTimeBehind = new int[lane_number][locations];
                int[][] literalCarFrontCat = new int[lane_number][locations];
                int[][] literalCarBehindCat = new int[lane_number][locations];
		int[][] literalSameFrontCat = new int[lane_number][locations];
                int[][] literalSameBehindCat = new int[lane_number][locations];

                for (int i = 0; i<lane_number; i++) {
                  for (int k = 0; k<locations; k++) {
                    timeFront[i][k] = new BooleanVar(store, "Time of arrival of car: [" +i+ ","+k+ "] greater than the front one");
                    timeBehind[i][k] = new BooleanVar(store, "Time of arrival of car: [" +i+ ","+k+ "] greater than the behind one");
                    satWrapper.register(timeFront[i][k]);
                    satWrapper.register(timeBehind[i][k]);
                    if(k < (locations-1)){
		    if((Integer.parseInt(arrival[i][k]) > Integer.parseInt(arrival[i][k+1])) && Integer.parseInt(arrival[i][k+1])!=0){
			literalTimeFront[i][k] = satWrapper.cpVarToBoolVar(timeFront[i][k], 1, true);
		    }
		    else {literalTimeFront[i][k] = satWrapper.cpVarToBoolVar(timeFront[i][k], 0, true);}}

                    if(k > 0){
		    if((Integer.parseInt(arrival[i][k]) > Integer.parseInt(arrival[i][k-1])) && Integer.parseInt(arrival[i][k-1])!=0){
			literalTimeBehind[i][k] = satWrapper.cpVarToBoolVar(timeBehind[i][k], 1, true);
			}
		    else {literalTimeBehind[i][k] = satWrapper.cpVarToBoolVar(timeBehind[i][k], 0, true);}}
                  }  
                }

                for (int i = 0; i<lane_number; i++) {
                  for (int k = 0; k<locations; k++) {
                    carFrontCat[i][k] = new BooleanVar(store, "Category of front car is higher than the category of car: [" +i+ ","+k+ "]");
		    carBehindCat[i][k] = new BooleanVar(store, "Category of the car behind is higher than the category of car: [" +i+ ","+k+ "]");
                    satWrapper.register(carFrontCat[i][k]);
                    satWrapper.register(carBehindCat[i][k]);
                    if(k < (locations-1)){
                      if(((category[i][k].charAt(0) > category[i][k+1].charAt(0)) && !parking[i][k+1].equals("__")) || parking[i][k].equals("__") || category[i][k].equals(category[i][k+1])){
                        literalCarFrontCat[i][k] = satWrapper.cpVarToBoolVar(carFrontCat[i][k], 0, true);
                      } 
			else{literalCarFrontCat[i][k] = satWrapper.cpVarToBoolVar(carFrontCat[i][k], 1, true);}
                    }
                    
                    if(k > 0){
		      if(((category[i][k].charAt(0) > category[i][k-1].charAt(0)) && !parking[i][k-1].equals("__")) || parking[i][k].equals("__") || category[i][k].equals(category[i][k-1])){
		        literalCarBehindCat[i][k] = satWrapper.cpVarToBoolVar(carBehindCat[i][k], 0, true);
                      } 
			else{literalCarBehindCat[i][k] = satWrapper.cpVarToBoolVar(carBehindCat[i][k], 1, true);}
                    }
                  }
                }

		for (int i = 0; i<lane_number; i++) {
                  for (int k = 0; k<locations; k++) {
                    sameFrontCat[i][k] = new BooleanVar(store, "Category is the same for car in front of car: [" +i+ ","+k+ "]");
                    sameBehindCat[i][k] = new BooleanVar(store, "Category is the same for car behind of car: [" +i+ ","+k+ "]");
                    satWrapper.register(sameFrontCat[i][k]);
                    satWrapper.register(sameBehindCat[i][k]);
                  if(k < (locations-1)){
                    if(category[i][k].equals(category[i][k+1]) && !parking[i][k+1].equals("__")){
                      literalSameFrontCat[i][k] = satWrapper.cpVarToBoolVar(sameFrontCat[i][k], 1, true);
                    }
                    else{literalSameFrontCat[i][k] = satWrapper.cpVarToBoolVar(sameFrontCat[i][k], 0, true);}}
                  if(k > 0){
                    if(category[i][k].equals(category[i][k-1]) && !parking[i][k-1].equals("__")){
                      literalSameBehindCat[i][k] = satWrapper.cpVarToBoolVar(sameBehindCat[i][k], 1, true);
                    }
                    else{literalSameBehindCat[i][k] = satWrapper.cpVarToBoolVar(sameBehindCat[i][k], 0, true);}}
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


		

		for (int i = 0; i<lane_number; i++) {
			for (int k = 0; k<locations; k++) {
				addClause(satWrapper, literalTimeFront[i][k]);
				addClause(satWrapper, literalTimeBehind[i][k]);
				addClause(satWrapper, literalCarFrontCat[i][k]);
				addClause(satWrapper, literalCarBehindCat[i][k]);
				addClause(satWrapper, literalSameFrontCat[i][k]);
				addClause(satWrapper, literalSameBehindCat[i][k]);	
			}
		}

                //Constraints
                for (int i = 0; i<lane_number; i++) {
                  for (int k = 0; k<locations; k++) {
                    addClause(satWrapper,literalCarFrontCat[i][k],literalCarBehindCat[i][k],literalSameFrontCat[i][k],literalSameBehindCat[i][k]); 
                    addClause(satWrapper,literalCarFrontCat[i][k],literalCarBehindCat[i][k],literalSameFrontCat[i][k],literalTimeBehind[i][k]);  
                    addClause(satWrapper,literalCarFrontCat[i][k],literalCarBehindCat[i][k],literalSameBehindCat[i][k],literalTimeFront[i][k]); 
                    addClause(satWrapper,literalCarFrontCat[i][k],literalCarBehindCat[i][k],literalSameBehindCat[i][k],literalTimeBehind[i][k]);
                  }
                }

                //Solve
                Search<BooleanVar> search = new DepthFirstSearch<BooleanVar>();
                SelectChoicePoint<BooleanVar> select = new SimpleSelect<BooleanVar>(allVariables,
                         new SmallestDomain<BooleanVar>(), new IndomainMin<BooleanVar>());
                Boolean result = search.labeling(store, select);

		if(result) System.out.println("TRAMADOOOOOOL: "+result);
		else{System.out.println("Fuck You");}


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
