#include <iostream>
#include <fstream>
#include <vector>
#include <string>


int main(int argc, char const *argv[]){

    // Check we have 3 parameters (name of the program + init map + final map)
    if (argc != 3) {
      std::cerr << "Wrong arguments.\nCorrect use:\n"
                << "./AstarParking <init-parking> <goal-parking>" << std::endl;
      return false;
    }

  std::vector <string> initVector;
  string initData;
  //open init map
  ifstream inFile(argv[1]);
  while(!inFile.eof()){
    inFile >> initData;
    initVector.push_back(initData);
  }
  //close init file
  inFile.close();

  std::vector <string> finVector;
  string finData;
  //open final map
  ifstream finFile(argv[2]);

  while(!finFile.eof()){
    finFile >> finData;
    finVector.push_back(finData);
  }
  //remove the end of file from the last position of the vector
  finVector.pop_back(finData);

  finFile.close();

  if(initVector[0] != finVector[0] || initVector[1] != finVector[1] ){
    std::cerr << "The input maps do not have the same size"<< std::endl;
    return false;
  }

  //check the maps have empty positions
  int checkEmpty(initVector, finVector);

  //vector to store the distance difference between car in first map and second map
  std::vector <int> distance;
  int rows = stoi(initVector[0]);
  int columns = stoi(initVector[1]);
  // int firstRow;
  // int firstCol;
  // int secRow;
  // int secCol;

  for(int i=0; i < initVector.size(); ++i){
    for(int j=0; j < finVector.size(); ++j){
      if(initVector[i] == finVector[j]){ //not sure
        distance.push_back(abs(j-i));
        // firstRow = i/columns;
        // firstCol = i%columns;
        // secRow = j/columns;
        // secCol = j%columns;
        // difRow = secRow - firstRow;
        // difCol = secCol - firstCol;
      }
    }
  }




    return 0;
}

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
    std::cerr << "There are no emppty spaces"<< std::endl;
    return -1;
    }
}
