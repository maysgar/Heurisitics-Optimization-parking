#include <iostream>
#include <fstream>
#include <vector>
#include <string>
#include <algorithm>

using namespace std;

struct node{
  int id;
  int f;
  int g;
  int h;
  std::vector<string> parking;
  node *parentNode;
  bool parent;
};

node compute_min(std::vector<node> set, int size);
int getHeuristic(std::vector<string> parking, std::vector<string> goal, int rows, int columns, string position);
std::vector<node> getNeighbours(node father, std::vector<string> goal, int rows, int columns, int id);

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

//method to print the map configurations
int printVectors(std::vector <string> init, int rows, int columns){
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

std::vector<node> astar_algorithm(std::vector<string> start, std::vector<string> goal, int rows, int columns){
  std::vector<node> openList;
  std::vector<node> closedList;
  std::vector<node> neighbours;
  std::vector<node> final_path;
  std::vector<node> fail;
  int idCount = 0;
  int aux;

  node startNode, goalNode;
  //Initialization of start node
  startNode.parking = start;
  startNode.id = idCount;
  startNode.parentNode = NULL;
  startNode.parent = false;
  //Set heuristic of start node by checking if car of the start parking input with respect to the goal 
  for(int i=0; i<rows; i++) for(int k=0; k<columns; k++){
    //TODO: HEURISTIC METHOD
    startNode.h += getHeuristic(start,goal,rows,columns,start[i*columns+k]);
  }
  startNode.g = 0;
  startNode.f = startNode.h + startNode.g;

  //Initialization of end node
  goalNode.id = -1;
  goalNode.parking = goal;
  goalNode.parent = true;

  //Insert in openList
  openList.push_back(startNode);

  while(!openList.empty()){
    node current;

    current = compute_min(openList,openList.size());

    //current has heuristic = 0 -> goal state
    if(current.h == 0){
      while(current.parent){
        final_path.push_back(current);
        current.parent = current.parentNode->parent;
      }
      final_path.push_back(current);
    return final_path;
    }

    // Erase from open list current expanded and add to close list
    for(int i=0; i<openList.size(); i++){
      if(openList[i].id == current.id) openList.erase(openList.begin()+i);
    }
    closedList.push_back(current);
    
    //Neighbours
    neighbours = getNeighbours(current,goal,rows,columns,idCount);
    for(int i=0; i<neighbours.size(); i++) openList.push_back(neighbours[i]);

    aux = 0;
    int tentative_gScore;
    for(int i=0; i<neighbours.size(); i++){
      for(int j=0; j<closedList.size(); j++){
        if(neighbours[i].parking == closedList[j].parking) ++aux;
       }
      //If neighbour's parking is already in closedList then skip the whole loop
      if(aux > 0) continue;
    
      for(int i=0; i<rows; i++) for(int j=0; j<columns; j++){
        for(int k=0; k<rows; k++) for(int l=0; l<columns; l++){
          tentative_gScore = current.g + getCost(neighbours[i].parking, k, l, i, j, columns);
        }
      }
      
      if(tentative_gScore >= neighbours[i].g) continue;

      neighbours[i].g = tentative_gScore;
      neighbours[i].f = neighbours[i].g + neighbours[i].h;      
    }// End neighbours for loop


  } //While loop
  return fail;
}

std::vector<node> getNeighbours(node father, std::vector<string> goal, int rows, int columns, int id){
  std::vector<node> children;
  node child;
  for(int i=0; i<rows; i++) for(int j=0; j<columns; j++){
    for(int k=0; k<rows; k++) for(int l=0; l<columns; l++){
      //If position that we are interested in is not empty and the spot that we want to move is empty...
      if(father.parking[i*columns+j]!="__" && father.parking[k*columns+l]=="__"){
	//TODO: GETCOST FUNCTION
        if(getCost(father.parking, k, l, i, j, columns) == -1){
	  
          child.id = id++;
	  //Update the grid of the child
          child.parking = father.parking;
          child.parking[k*columns+l]=child.parking[i*columns+j];
          child.parking[i*columns+j]="__";

  	  child.parentNode = &father;
          child.parent = true;
          child.g = getCost(father.parking, k, l, i, j, columns) + father.g;

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

node compute_min(std::vector<node> set, int size){
  node min;
  min.f = set[0].f;
  for (int i=0; i<size; i++) {
    if(set[i].f <= min.f){
      min.id = set[i].id;
      min.f = set[i].f;
      min.g = set[i].g;
      min.h = set[i].h;
      min.parking = set[i].parking;
      min.parent = set[i].parent;
      min.parentNode = set[i].parentNode;
    }
  }
  return min;
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
    if(goal[i*columns+j]==position){
      finRow=i;
      finCol=j;
      break;
    }
  }

  return abs(inRow-finRow)+abs(inCol-finCol);
}

int main(int argc, char const *argv[]){

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

  std::cout << "Initial map" << std::endl;
  printVectors(initVector, rows, columns);
  std::cout << "Final map" << std::endl;
  printVectors(finVector, rows, columns);

  astar_algorithm(initVector,finVector,rows,columns);

  return 0;
}
