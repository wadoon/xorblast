/*
  This program is free software: you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation, either version 3 of the License, or
  (at your option) any later version.

  This program is distributed in the hope that it will be useful, but
  WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
  General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with this program. If not, see <http://www.gnu.org/licenses/>.
*/

#include <stdlib.h>
#include <m4ri/m4ri.h>
#include <vector>
#include <string>
#include <iostream>
#include <fstream>
#include <sstream>
#include <getopt.h>
#include <unordered_map>

using namespace std;

typedef unordered_map<unsigned int, unsigned int> intmap;

// -- GLOBALS ------------------------------------------------------------------
const auto VERSION = "0.9-beta";
const auto AUTHOR  = "Alexander Weigl <weigl@kit.edu>";


//!
vector<vector<int>> xor_clauses;

//! Number of variables
unsigned int nvars = 0;

//! Number of clauses
unsigned int nclauses = 0;

/**
 * Options and flags
 */
bool    verbose      = false;
bool    write_output = false;
string  output_file;
string  input_file;
bool    gauss        = true;

// -- Functions  ---------------------------------------------------------------

void print_usage() {
    cout << "xorblast -- Preprocessing for XOR clauses\n"
         << "\n"
         << "Usage: xorblast [-v] [-o output] input\n"
         << "\n"
         << "Options:\n"
         << "  -v\tverbose output\n"
         << "  -g,-G\tenable or disable gauss elimination, default: enabled\n"
         << "  -o\toutput file written\n"
         << "  -h\tthis help message\n"
         << "\n\n"
         << "Author: Alexander Weigl <weigl@kit.edu>\n"
         << "        Institute for Theoretical Informatics\n"
         << "        Karlsruhe Institute of Technology"
         << endl;
}

void parse_cli(int argc, char* argv[]) {
    int c, option_index;
    while((c = getopt(argc, argv, "hgGvo:")) != -1) {
        switch(c) {
        case 'h':
            print_usage();
            exit(0);
            break;
        case 'g':
            gauss = true;
            break;
        case 'G':
            gauss = false;
            break;
        case 'v':
            verbose = true;
            break;
        case 'o':
            write_output = true;
            output_file = optarg;
            if(verbose)  cout << "c output file: " << output_file << endl;
            break;
        case '?':
            cout << "c Unkown option. exit" << endl;
            exit(2);
        }
    }

    if (optind < argc) {
        input_file = argv[optind];
        if(verbose) cout << "c input file: " << input_file << endl;
    } else {
        cout << "c input file not given" << endl;
        exit(1);
    }
}

void parse_xor_clause(ifstream& input) {
    vector<int> clause;
    while(true) {
        int lit;
        input >> lit;

        if(lit == 0)
            break;

        clause.push_back(lit);
    }

    xor_clauses.push_back(clause);

    if(verbose)  {
        cout << "c found xor clause: ";
        for(auto l : clause) cout << l << " ";
        cout << endl;
    }
}

void read(const string& filename) {
    ifstream input;
    input.open(filename);

    if(verbose)
        cout << "c read " << filename << endl;

    //Buffering
    //const unsigned length = 8192;
    //char buffer[length];
    //input.rdbuf()->pubsetbuf(buffer, length);

    input.seekg(1+1+3+1);

    input >> nvars;
    input >> nclauses;

    if(verbose)
        cout << "c vars: " << nvars << " clauses: " << nclauses <<endl;

    char c;
    while(! input.eof() ) {
        input.get(c);
        if(c == '\n') {
            input.get(c);
            if(c == 'x') {
                parse_xor_clause(input);
            }
        }
    }
}

int tseitin_xor(int a, int b, ostream& out) {
    if(verbose) cout << "c tseiting of " << a << " " << b << endl;
    nclauses += 4;

    /* WolframAlpha:
       z <-> (a xor b) ===
           (-a OR -b OR -z)
       AND (-a OR  b OR  z)
       AND ( a OR -b OR  z)
       AND ( a OR  b OR -z)
    */

    int z = ++nvars;
    out << -z << ' ' <<  a << ' ' <<  b << " 0\n"
        << -z << ' ' << -a << ' ' << -b << " 0\n"
        <<  z << ' ' << -a << ' ' <<  b << " 0\n"
        <<  z << ' ' <<  a << ' ' << -b << " 0\n";
    return z;
}

void tseitin_xor(const vector<int>& xclause,
                 ostream& output) {

    auto iter = xclause.begin();
    auto end = xclause.end();

    auto a = *iter++;
    auto b = *iter++;
    auto q = tseitin_xor(a, b, output);

    for(; iter != end; iter++) {
        q = tseitin_xor(q, *iter, output);
    }

    output << q << " 0\n";
}

string recode() {
    stringstream output;

    for(auto& xclause : xor_clauses) {
        switch(xclause.size()) {
        case 0:
            continue; // empty clause
        case 1:
            output <<  xclause.at(0) << " 0\n";
            break;
        default:
            tseitin_xor(xclause, output);
            break;
        }
    }
    return output.str();
}

void print_matrix(mzd_t* M) {
    for(int row = 0; row < M->nrows; row++) {
        cout << "c ";
        for (int col= 0 ; col < M->ncols; col++) {
            cout << mzd_read_bit(M, row, col);
            if(M->ncols - 2 == col) cout << ':';
        }
        cout << endl;
    }
}

void simplify() {
    intmap ind_to_pvar;
    intmap pvar_to_ind;

    // map variables to matrix indices
    unsigned int ind = 0;
    for(auto& clause : xor_clauses){
        for(auto& lit : clause) {
            unsigned int var = abs(lit);
            if(pvar_to_ind.find(var) == pvar_to_ind.end()) {
                // assign
                pvar_to_ind[var] = ind;
                ind_to_pvar[ind] = var;

                if(verbose) {
                    cout << "c " << ind << " <--> " << var << endl;
                }

                ind++;
            }
        }
    }

    // initialize the matrix, with rows and cols
    // one extra column for desired result [A; b]
    mzd_t *M = mzd_init( xor_clauses.size(), 1 + pvar_to_ind.size()  );

    // translate xor clauses into matrix
    int row = 0;
    for(auto& clause : xor_clauses){
        for(auto& lit : clause) {

            // every variable is an one in the matrix A[row, vti(var)] = 1
            unsigned int var = abs(lit);
            auto col = pvar_to_ind[var];
            mzd_write_bit(M, row, col, 1);
        }

        // set last column to 1, if want an xor (positive first literal)
        // otherwise it will keep 0 for equivalence.
        if(clause[0] > 0) {
            mzd_write_bit(M, row, M->ncols - 1, 1);
        }

        row++;
    }

    if(verbose) {
        print_matrix(M);
        cout << "c -------------" << endl;
    }

    rci_t re = mzd_echelonize_naive(M, 1);

    if(verbose) {
        print_matrix(M);
    }

    //translate back into clausel form
    xor_clauses.clear();

    for (int row = 0; row < M->nrows; row++) {
        vector<int> clause;

        for(int col = 0; col < M->ncols - 1; col++) {
            auto var = ind_to_pvar[col];
            if(mzd_read_bit(M, row, col) == 1)
                clause.push_back(var);
        }

        if(clause.size() > 0) {
            if(mzd_read_bit(M, row, M->ncols -1) == 0) {
                clause[0] *= -1;
            }
            xor_clauses.push_back(clause);
            if(verbose){
                cout << "x ";
                for(auto& l : clause) cout << l << " ";
                cout << "0" << endl;
            }
        }
    }

    mzd_free(M);
}

void read_and_manipulate(const string& cnf) {

    ifstream input;
    ofstream output;

    input.open(input_file);
    output.open(output_file);

    string line;

    getline(input, line); // throw away first line

    output << "p cnf " << nvars << " " << nclauses << endl;

    while(getline(input, line)) {
        if(line[0] == 'x')
            continue;
        output << line <<"\n";
    }
    output << cnf;

    input.close();
    output.close();
}

int main(int argc, char* argv[]) {
    parse_cli(argc, argv);
    read(input_file);

    if(gauss)
        simplify();

    auto cnf = recode();

    if(write_output) {
        read_and_manipulate(cnf);
    } else {
        cout << cnf;
    }
}
