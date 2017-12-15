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

public class SATParking2 {
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

                BooleanVar[] a = new BooleanVar[lane_number*locations];
                BooleanVar[] b = new BooleanVar[lane_number*locations];
                BooleanVar[] c = new BooleanVar[lane_number*locations];
                BooleanVar[] empty = new BooleanVar[lane_number*locations];
		int literalA
		int literalB
		int literalC	
		int literalEmpty

		BooleanVar[] allVariables = new BooleanVar[lane_number*locations];
		int count = 0;

		for (int i = 0; i<lane_number; i++) {
                  	for (int k = 0; k<locations; k++) {
				allVariables[count] = a[i][k];
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
}

