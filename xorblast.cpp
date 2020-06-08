/*******************************************************************************
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
********************************************************************************/

#include <stdlib.h>
#include <m4ri/m4ri.h>
#include <vector>
#include <string>
#include <iostream>
#include <fstream>
#include <sstream>
#include <getopt.h>
#include <unordered_map>
#include <assert.h>

using namespace std;

typedef unordered_map<unsigned int, unsigned int> intmap;

// -- GLOBALS ------------------------------------------------------------------
const auto VERSION = "1.0";
const auto AUTHOR  = "Alexander Weigl <weigl@kit.edu>";


//! the catched xor clauses
vector<vector<int>> xor_clauses;

//! Number of variables
unsigned int nvars = 0;

//! Number of clauses
unsigned int nclauses = 0;

/**
 * Options and flags
 */
bool        verbose      = false;
bool        write_output = false;
string      output_file;
string      input_file;
bool        gauss        = true;
bool        smt_check    = false;
std::string smt_file;

// -- Functions  ---------------------------------------------------------------

void print_usage() {
    cout << "xorblast -- Preprocessing for XOR clauses\n"
         << "\n"
         << "Usage: xorblast [-v] [-o output] input\n"
         << "\n"
         << "Options:\n"
         << "  -v\tverbose output\n"
         << "  -g,-G\tenable or disable gauss elimination, default: enabled\n"
         << "  -s FILE\tsmt check of gauss elimination"
         << "  -o\toutput file written\n"
         << "  -h\tthis help message\n"
         << "\n\n"
         << "Author: Alexander Weigl <weigl@kit.edu>\n"
         << "        Institute for Theoretical Informatics\n"
         << "        Karlsruhe Institute of Technology\n"
         << "Version: " << VERSION
         << endl;
}

void parse_cli(int argc, char* argv[]) {
    int c, option_index;
    while((c = getopt(argc, argv, "hgGvo:s:")) != -1) {
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
        case 's':
            smt_check = true;
            smt_file = optarg;
            if(verbose)  cout << "c smt file: " << smt_file << endl;
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
            if(input.peek() == 'x') {
                input.get(c);//consume x
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


// -----------------------------------------------------------------------------
// True xor blasting, suitable for small instances and if equivalence should be
// maintained


// https://stackoverflow.com/questions/109023/how-to-count-the-number-of-set-bits-in-a-32-bit-integer
uint32_t num_of_bits(uint32_t i)
{
     i = i - ((i >> 1) & 0x55555555);
     i = (i & 0x33333333) + ((i >> 2) & 0x33333333);
     return (((i + (i >> 4)) & 0x0F0F0F0F) * 0x01010101) >> 24;
}

void decode(uint32_t num, const vector<int> xclause, ostream& output) {
    for(uint32_t i = 0; i < xclause.size();  i++, num>>=1) {
        if((num&1)>0) {
            output << abs(xclause.at(i)) << " ";
        }
        else {
            output << "-" << abs(xclause.at(i)) << " ";
        }
    }

    output << "0\n";
}


void xorblast(const vector<int>& xclause, ostream& output) {
    assert(xclause.size() <= 31);
    uint32_t M = pow(2, xclause.size() );

    // even or odd parity
    int mode = xclause.at(0) < 0 ? 0 : 1;

    for(uint32_t i = 0; i < M; i++) {
        if( num_of_bits(i)%2 == mode) {
            decode(i, xclause, output);
        }
    }
}
// -----------------------------------------------------------------------------


void tseitin_xor(const vector<int>& xclause,
                 ostream& output) {

    auto iter = xclause.begin();
    auto end = xclause.end();

    auto a = *iter++;
    auto b = *iter++;
    auto q = tseitin_xor(abs(a), b, output);

    for(; iter != end; iter++) {
        q = tseitin_xor(q, *iter, output);
    }

    output << ((a<0)?-q:q) << " 0\n";
}

string recode() {
    stringstream output;

    bool equiv_flag = true;

    for(auto& xclause : xor_clauses) {
        switch(xclause.size()) {
        case 0:
            continue; // empty clause
        case 1:
            output <<  xclause.at(0) << " 0\n";
            break;
            // case 2:
            //     tseitin_xor_2(xclause, output);
            //     break;
            // case 3:
            //     tseitin_xor_3(xclause, output);
            //     break;
            // case 4:
            //     tseitin_xor_4(xclause, output);
            //     break;
            // case 5:
            //     tseitin_xor_5(xclause, output);
            //     break;
        default:
            tseitin_xor(xclause, output);
            equiv_flag = false;
            break;
        }
    }

    if(equiv_flag && verbose) {
        cout << "c Equivalent transformations" << endl;
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

void to_smt(stringstream& smt) {
    smt << "(and ";
    for(auto& clause : xor_clauses) {
        if(clause.size() == 1) {
            auto lit = clause.at(0);
            if(lit < 0)
                smt << "(not a" << abs(lit) <<  ") ";
            else
                smt << "a" << abs(lit) << " ";
            continue;
        }

        smt << "(xor ";
        for(auto& lit : clause) {
            if(lit < 0)
                smt << "(not a" << abs(lit) <<  ") ";
            else
                smt << "a" << lit << " ";
        }
        smt << ")" << endl;
    }
    smt << ")"<<endl;
}

void simplify() {
    intmap ind_to_pvar;
    intmap pvar_to_ind;

    stringstream smt;
    for(uint32_t var = 0; var <= nvars; var++)
        smt << "(declare-fun a" << var << " () Bool)" << endl;

    // map variables to matrix indices
    unsigned int ind = 0;
    for(auto& clause : xor_clauses) {
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


    smt << "(assert (not (= " << endl;
    to_smt(smt);


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

	    // set last column to 1, if want an xor (positive
	    // first literal) otherwise it will keep 0 for
	    // equivalence.
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
        } else {
            if(mzd_read_bit(M, row, M->ncols - 1) == 1) {
                cout << "!!! XOR CONSTRAINTS CONTRADICT !!!"<< endl;
                exit(42);
            }
        }
    }

    to_smt(smt);
    smt << ")))\n(check-sat)\n(get-model)"<< endl;
    mzd_free(M);


    if(smt_check) {
        ofstream sf(smt_file);
        sf << smt.str();
        //        cout << smt.str();
    }
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
