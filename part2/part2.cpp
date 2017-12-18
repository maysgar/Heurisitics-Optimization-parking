#include <iostream>
#include <fstream>
#include <vector>
#include <string>

using namespace std;

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
    std::cerr << "There are no emppty spaces"<< std::endl;
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

//method to generate the vectors of the maps
/*void fillVector(std::vector <string> vector, ifstream file){
  string data;
  //open final map;

  while(!file.eof()){
    file >> data;
    vector.push_back(data);
  }
  //close file
  file.close();
  //erase the first two positions of the vector (rows and columns)
  vector.erase(vector.begin());
  vector.erase(vector.begin());
  //remove the end of file from the last position of the vector
  vector.pop_back();
}*/
 

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

  int rows = stoi(initVector[0]);
  int columns = stoi(initVector[1]);

  //erase the first two positions of the vector (rows and columns)
  initVector.erase(initVector.begin());
  initVector.erase(initVector.begin());
  //remove the end of file from the last position of the vector
  initVector.pop_back();
  

  std::vector <string> finVector;
  string finData;
  //open final map
  ifstream finFile(argv[2]);

  while(!finFile.eof()){
    finFile >> finData;
    finVector.push_back(finData);
  }
  //close file
  finFile.close();
  //erase the first two positions of the vector (rows and columns)
  finVector.erase(finVector.begin());
  finVector.erase(finVector.begin());
  //remove the end of file from the last position of the vector
  finVector.pop_back();

  //check the maps have empty positions
  checkEmpty(initVector, finVector);

  //vector to store the distance difference between car in first map and second map
  std::vector <int> distance;
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

  std::cout << "Initial map" << std::endl;
  printVectors(initVector, rows, columns);
  std::cout << "Final map" << std::endl;
  printVectors(finVector, rows, columns);

  

  return 0;
}

