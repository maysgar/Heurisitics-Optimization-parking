#include <iostream>
#include <fstream>
#include <vector>
#include <string>
#include <algorithm>
#include <chrono>

using namespace std;

struct node{
  int id;
  int f;
  int g;
  int h;
  std::vector<string> parking;
  int parentNode;
  bool parent;
};

void printVectors(std::vector<string> init, int rows, int columns);
node compute_min(std::vector<node> a, int size);
int getHeuristic(std::vector<string> parking, std::vector<string> goal, int rows, int columns, string position);
std::vector<node> getNeighbours(node father, std::vector<string> goal, int rows, int columns, int id);
int getCost(vector <string> parking, int lane_number, int loc, int initial_lane_number, int initial_loc, int locations);
void printInfo(std::vector<node> final_path, int cost, int size);

//method to make sure the maps have empty spots
int checkEmpty(std::vector <string> init, std::vector <string> fin){
  int initEmpty = 0;
  int finEmpty = 0;
  for(int i= 0; i < init.size(); ++i){
    if(init[i] == "__"){
      ++initEmpty;
    }
    if(fin[i] == "__"){
      ++finEmpty;
    }
  }
  if(initEmpty == 0 || finEmpty == 0){
    std::cerr << "There are no emzppty spaces"<< std::endl;
    return -1;
    }
}

std::vector<node> astar_algorithm(std::vector<string> start, std::vector<string> goal, int rows, int columns){
  std::vector<node> openList;
  std::vector<node> closedList;
  std::vector<node> neighbours;
  std::vector<node> final_path;
  int idCount = 0;

  node startNode, goalNode;
  //Initialization of start node
  startNode.parking = start;
  startNode.id = idCount;
  startNode.parentNode = -1;
  startNode.parent = false;
  //Set heuristic of start node by checking if car of the start parking input with respect to the goal 
  startNode.h = 0;
  for(int i=0; i<rows; i++) for(int k=0; k<columns; k++){
    startNode.h += getHeuristic(start,goal,rows,columns,start[i*columns+k]);
  }
  startNode.g = 0;
  startNode.f = startNode.h + startNode.g;

  //Insert in openList
  openList.push_back(startNode);

  while(!openList.empty()){
    node current;
    int min;

    current = compute_min(openList,openList.size());

    cout << "Heuristic: " << current.h << endl;
    printVectors(current.parking,rows,columns);

    //current has heuristic = 0 -> goal state
    if(current.h == 0){
      while(current.parent){
        final_path.push_back(current);
        for(int i=0; i<closedList.size(); i++){
            if(current.parentNode==closedList[i].id) current = closedList[i];
	}
      }
      final_path.push_back(current);
     
    printInfo(final_path, final_path[0].g, openList.size());
    return final_path;
    }

    // Erase from open list current expanded and add to close list
    for(int j=0; j<openList.size(); j++){
      if(current.parking == openList[j].parking) openList.erase(openList.begin()+j);
    }
    closedList.push_back(current);
    
    //Neighbours  
    neighbours = getNeighbours(current,goal,rows,columns,idCount);  
    idCount = neighbours[neighbours.size()-1].id;

    for (int i=0; i<neighbours.size(); i++) {
    int aux = 0;
      for(int j=0; j<closedList.size(); j++){
        int aux_ = 0;
        for(int k=0; k<rows; k++) for(int l=0; l<columns; l++){
            if(neighbours[i].parking[k*columns+l]!=closedList[j].parking[k*columns+l]) aux_++;
        }
        if(aux_!=0) aux++;
      }
      if(aux==closedList.size()) openList.push_back(neighbours[i]);
    }
  } //While loop
  

  return final_path;
}

//method to print the map configurations
void printVectors(std::vector <string> init, int rows, int columns){
  std::cout << "\n";
  int j = 0;
  for(int i = 0; i < rows; ++i){
       for(int j = 0; j < columns; ++j){
          std::cout << init[i*columns+j] << " ";
     }
  std::cout << "\n";
  }
 std::cout << "\n";
}

std::vector<node> getNeighbours(node father, std::vector<string> goal, int rows, int columns, int id){
  std::vector<node> children;
  node child;
  for(int i=0; i<rows; i++) for(int j=0; j<columns; j++){
    for(int k=0; k<rows; k++) for(int l=0; l<columns; l++){
      //If position that we are interested in is not empty and the spot that we want to move is empty...
      if(father.parking[i*columns+j]!="__" && father.parking[k*columns+l]=="__"){
        if(getCost(father.parking, k, l, i, j, columns) != -1){
	  
          child.id = id++;
	  //Update the grid of the child
          child.parking = father.parking;
          child.parking[k*columns+l]=child.parking[i*columns+j];
          child.parking[i*columns+j]="__";

  	  child.parentNode = father.id;
          child.parent = true;
          child.g = getCost(father.parking, k, l, i, j, columns) + father.g;
          child.h = 0;

	  for(int m=0; m<rows; m++) for(int n=0; n<columns; n++){
            child.h += getHeuristic(child.parking,goal,rows,columns,child.parking[m*columns+n]);
          }

          child.f = child.h + child.g;
	  children.push_back(child);
        }
      }
    }
  }
  return children;
}

node compute_min(vector<node> a, int size){
  node min;
  min.f = a[0].f;
  for(int i=0; i<size; i++){
    min.id = a[i].id;
    min.f = a[i].f;
    min.g = a[i].g;
    min.h = a[i].h;
    min.parking = a[i].parking;
    min.parentNode = a[i].parentNode;
    min.parent = a[i].parent;
  }
  return min;
}

// This cost function has been developed by Fernando Garcia Sanz & Antonio de Padua & Ismael Garrido & Gabriel Garcia.
int getCost(vector <string> parking, int lane_number, int loc, int initial_lane_number, int initial_loc, int locations){
  int checker = 0;
        if(lane_number==initial_lane_number) { //Same lane
                if(loc>initial_loc) { //Final location bigger than initial
                  for(int i = initial_loc+1; i<loc; i++){
                    if(parking[lane_number*locations+i]!="__"){ //Check if blocked for that location
                      if(loc==locations-1){ //If location is final one, check the other way
                        for(int j = initial_loc-1; j>-1; j--){
                          if(parking[lane_number*locations+j]!="__"){
                              return -1;
                            }
                        }
                        return 4;
                      }
                        return -1;
                      }
                    }
                    return 1; //Possible grid -> forward in same lane
                  }
                else if(loc<initial_loc){
                  for(int i = initial_loc-1; i>loc; i--){
                    if(parking[lane_number*locations+i]!="__"){
                      if(loc==0){
                        for(int j = initial_loc+1; j<locations; j++){
                          if(parking[lane_number*locations+j]!="__"){
                            return -1;
                          }
                        }
                        return 3;
                      }
                        return -1;
                      }
                  }
                  return 2; //Possible grid -> backwards in same lane
                }
        }
        else{
          //Check if a final position on its line can be reached
          for(int i = initial_loc+1; i<locations; i++){
            if (parking[initial_lane_number*locations+i]!="__"){
              checker = 1; //Set one if it is blocked by this side
            }
          }
          for(int i = initial_loc-1; i>-1; i--){
            if (parking[initial_lane_number*locations+i]!="__"){
              if(checker==1){ //If blocked by one side and also blocked for this, set checker equal two
                checker=2;
              }
            }
          }
          if(checker==2){ //If blocked by two sides, no possible grid
            return -1;
          }
          else{
            if(loc==0) { //Possible grid -> first position of another lane
                    return 3;
            }
            else if(loc==locations-1) { //Possible grid -> last position of another lane
                    return 4;
            }
          }
        }
        return -1;
}

int getHeuristic(std::vector<string> parking, std::vector<string> goal, int rows, int columns, string position){
  int h;
  int inRow;
  int inCol;
  int finRow;
  int finCol;

  for(int i = 0; i < rows; i++) for (int j = 0; j < columns; j++){
    if(parking[i*columns+j]==position){
      inRow=i;
      inCol=j;
      break;
    }
  }
  for(int i = 0; i < rows; i++) for (int j = 0; j < columns; j++){
    if(goal[i*columns+j]==position){
      finRow=i;
      finCol=j;
      break;
    }
  }

  return abs(inRow-finRow)+abs(inCol-finCol);
}

void printInfo(std::vector<node> final_path, int cost, int size){
  ofstream outfile("result.info");
  outfile << "Step length: "<< final_path << endl;
  outfile << "Running time (seconds): "<< endl;
  outfile << "Total cost: "<< cost << endl;
  outfile << "Expansions: "<< size << endl; 
  // Close the file
  outfile.close();
}

int main(int argc, char const *argv[]){

    using clk = std::chrono::high_resolution_clock;
    auto t1 = clk::now();

    // Check we have 3 parameters (name of the program + init map + final map)
    if (argc != 3) {
      std::cerr << "Wrong arguments.\nCorrect use:\n"
                << "./AstarParking <init-parking> <goal-parking>" << std::endl;
      return false;
    }

  std::vector <string> initVector;
  std::vector <string> finVector;
  string initData;
  string finData;

  //open init map
  ifstream inFile(argv[1]);
  while(!inFile.eof()){
    inFile >> initData;
    initVector.push_back(initData);
  }
  //close init file
  inFile.close();

  //open final map
  ifstream finFile(argv[2]);
  while(!finFile.eof()){
    finFile >> finData;
    finVector.push_back(finData);
  }
  //close file
  finFile.close();

  int rows = stoi(initVector[0]);
  int columns = stoi(initVector[1]);

  initVector.erase(initVector.begin());
  finVector.erase(finVector.begin());
  initVector.erase(initVector.begin());
  finVector.erase(finVector.begin());

  initVector.pop_back();
  finVector.pop_back();

  //check the maps have empty positions
  checkEmpty(initVector, finVector);
  vector<node> result;

  result = astar_algorithm(initVector,finVector,rows,columns);
  cout << "Size of result of A*: " << result.size() << endl;
  
  auto t2 = clk::now();
  auto diff = std::chrono::duration_cast<std::chrono::microseconds>(t2 - t1);

  for(int i=0; i<result.size(); i++) printVectors(result[i].parking,rows,columns);

  return 0;
}
