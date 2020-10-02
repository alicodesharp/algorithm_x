// C++ program for solving exact cover problem 
// using DLX (Dancing Links) technique 

#include <bits/stdc++.h> 

#define MAX_ROW 100 
#define MAX_COL 100 

using namespace std;
using namespace std::chrono;


/**
 * comb_funcs.h
 *
 * By Sebastian Raaphorst, 2018.
 *
 * Simple combinatorial functions.
 */


#include <array>
#include <cstddef>
#include <iostream>
#include <optional>
#include "dlx_contexpr.h"

namespace cmath {
    using factype = unsigned long long;

    /**
     * Binomial coefficient.
     * @param n
     * @param r
     * @return (n choose r)
     */
    constexpr factype nCr(factype n, factype r) noexcept {
        if (n < r)
            return 0;

        factype bigger = n - r > r ? n - r : r;

        factype f = 1;
        for (factype i = n; i > bigger; --i)
            f *= i;
        for (factype i = (n - bigger); i >= 1; --i)
            f /= i;
        return f;
    }

    /**
     * Given a k-subset of the v-set [v], find its rank in lexicographical order.
     * @tparam v the size of the base set
     * @tparam k the size of the subset
     * @param k-set the k-set to rank
     * @return the rank of k-set
     */
    template<factype v, factype k>
    constexpr factype rankKSubset(const std::array<factype, k> &kset) noexcept {
        factype r = nCr(v, k);
        for (int i = 0; i < k; ++i)
            r -= nCr(v - kset[i] - 1, k - i);
        return r - 1;
    }

    /**
     * Given a valid rank, i.e. 0 <= rk < nCr(v k), find the k-set it counts in lexicographical order.
     * @tparam v the size of the base set
     * @tparam k the size of the subset
     * @param rank the rank of the k-set
     * @return the k-set
     */
    template<factype v, factype k>
    constexpr std::array<factype, k> unrankKSubset(factype rank) noexcept {
        std::array<factype, k> kset{};

        factype vi = nCr(v, k);
        factype j = v;
        factype ki = k;
        factype s = rank + 1;

        for (factype i = 0; i < k - 1; ++i) {
            while (s > vi - nCr(j, ki))
                --j;
            kset[i] = v - j - 1;

            s += nCr(j + 1, ki) - vi;
            --ki;
            vi = nCr(j, ki);
        }

        kset[k - 1] = v + s - vi - 1;
        return std::move(kset);
    }

    /**
     * Given a k-set as a subset of the v-set [v], return its successor, if one exists.
     * (If not, the behaviour is undefined.)
     *
     * @tparam v the size of the base set
     * @tparam k the size of the subset
     * @param kset the k-set whose successor we want
     * @return the k-set that is the successor of kset under lexicographical ordering
     */
    template<factype v, factype k>
    constexpr std::array<factype, k> succKSubset(std::array<factype, k> kset) noexcept {
        for (factype i = k-1; i >= 0; --i) {
            ++kset[i];
            if (kset[i] < v && kset[i] + (k - i) <= v) {
                for (factype j = i + 1; j < k; ++j)
                    kset[j] = kset[i] + j - i;
                break;
            }
        }

        return kset;
    }


    /**
     * Create a formulation of a t-(v, k, 1) design.
     * The columns are the t-sets, of which there are C(v, t).
     * The rows are the k-sets, with position <r,c> indicating that the rth k-set contains thhe cth t-set.
     *
     * We have:
     * 1. C(v, t) cols
     * 2. C(v, k) rows
     * 3. C(v, k) * C(k, t) entries.
     */
    template<size_t v, size_t k, size_t t,
            size_t cols = nCr(v, t),
            size_t rows = nCr(v, k),
            size_t nodes_per_row = nCr(k, t),
            size_t nodes = rows * nodes_per_row>
    constexpr dlx::position_array<nodes> makeDesignPositions() noexcept {
        dlx::position_array<nodes> array{};

        // Keep track of the current node.
        int node = 0;
        for (int row = 0; row < rows; ++row) {
            const auto kset = unrankKSubset<v, k>(row);

            for (int col = 0; col < nodes_per_row; ++col) {
                const auto tsetIdx = unrankKSubset<k, t>(col);

                // We need to translate tsetIdx into a subset of k-set.
                std::array<factype, t> tset{};
                for (int i = 0; i < t; ++i)
                    tset[i] = kset[tsetIdx[i]];
                const auto tsetRk = rankKSubset<v, t>(tset);

                // Now we add a node, namely (row, tsetRk).
                // In order to mark this methhod constexpr, we need to assign to first and second individually.
                array[node].first = row;
                array[node].second = tsetRk;
                ++node;
            }
        }

        return std::move(array);
    }

    /**
     * A convenience method to run DLX for a t-design and return the solution.
     * @tparam v v parameter
     * @tparam k k parameter
     * @tparam t t parameter
     * @return the solution as an optional
     */
    template<size_t v, size_t k, size_t t,
            const auto cols = nCr(v, t),
            const auto rows = nCr(v, k),
            const auto nodes_per_row = nCr(k, t),
            const auto nodes = rows * nodes_per_row>
    constexpr std::optional<std::array<bool, rows>> run_t_design() noexcept {
        // Solve, all constexpr!
        return dlx::DLX<cols, rows, nodes>::run(makeDesignPositions<v, k, t>());
    }

    /**
     * A convenience method to print a solution for a t-design problem.
     * Note that t is unnecessary for printing.
     *
     * @tparam v v parameter
     * @tparam k k parameter
     * @param solution the solution returned by DLX
     */
    template<size_t v,
            size_t k,
            const auto rows = nCr(v, k)>
    void print_solution(const std::optional<std::array<bool, rows>> &solution) noexcept {
        for (factype i = 0; i < rows; ++i)
            if ((*solution)[i]) {
                auto kset = unrankKSubset<v, k>(i);
                for (const auto &e: kset)
                    std::clog << e << ' ';
                std::clog << '\n';
            }
        std::flush(std::clog);
    }
}
struct Node 
{ 
public: 
	struct Node *left; 
	struct Node *right; 
	struct Node *up; 
	struct Node *down; 
	struct Node *column; 
	int rowID; 
	int colID; 
	int nodeCount; 
}; 

// Header node, contains pointer to the 
// list header node of first column 
struct Node *header = new Node(); 

// Matrix to contain nodes of linked mesh 
struct Node Matrix[MAX_ROW][MAX_COL]; 

// Problem Matrix 
bool ProbMat[MAX_ROW][MAX_COL]; 

// vector containing solutions 
vector <struct Node*> solutions; 

// Number of rows and columns in problem matrix 
int nRow = 0,nCol = 0; 


// Functions to get next index in any direction 
// for given index (circular in nature) 
int getRight(int i){return (i+1) % nCol; } 
int getLeft(int i){return (i-1 < 0) ? nCol-1 : i-1 ; } 
int getUp(int i){return (i-1 < 0) ? nRow : i-1 ; } 
int getDown(int i){return (i+1) % (nRow+1); } 

// Create 4 way linked matrix of nodes 
// called Toroidal due to resemblance to 
// toroid 
Node *createToridolMatrix() 
{ 
	// One extra row for list header nodes 
	// for each column 
	for(int i = 0; i <= nRow; i++) 
	{ 
		for(int j = 0; j < nCol; j++) 
		{ 
			// If it's 1 in the problem matrix then 
			// only create a node 
			if(ProbMat[i][j]) 
			{ 
				int a, b; 

				// If it's 1, other than 1 in 0th row 
				// then count it as node of column 
				// and increment node count in column header 
				if(i) Matrix[0][j].nodeCount += 1; 

				// Add pointer to column header for this 
				// column node 
				Matrix[i][j].column = &Matrix[0][j]; 

				// set row and column id of this node 
				Matrix[i][j].rowID = i; 
				Matrix[i][j].colID = j; 

				// Link the node with neighbors 

				// Left pointer 
				a = i; b = j; 
				do{ b = getLeft(b); } while(!ProbMat[a][b] && b != j); 
				Matrix[i][j].left = &Matrix[i][b]; 

				// Right pointer 
				a = i; b = j; 
				do { b = getRight(b); } while(!ProbMat[a][b] && b != j); 
				Matrix[i][j].right = &Matrix[i][b]; 

				// Up pointer 
				a = i; b = j; 
				do { a = getUp(a); } while(!ProbMat[a][b] && a != i); 
				Matrix[i][j].up = &Matrix[a][j]; 

				// Down pointer 
				a = i; b = j; 
				do { a = getDown(a); } while(!ProbMat[a][b] && a != i); 
				Matrix[i][j].down = &Matrix[a][j]; 
			} 
		} 
	} 

	// link header right pointer to column 
	// header of first column 
	header->right = &Matrix[0][0]; 

	// link header left pointer to column 
	// header of last column 
	header->left = &Matrix[0][nCol-1]; 

	Matrix[0][0].left = header; 
	Matrix[0][nCol-1].right = header; 
	return header; 
} 

// Cover the given node completely 
void cover(struct Node *targetNode) 
{ 
	struct Node *row, *rightNode; 

	// get the pointer to the header of column 
	// to which this node belong 
	struct Node *colNode = targetNode->column; 

	// unlink column header from it's neighbors 
	colNode->left->right = colNode->right; 
	colNode->right->left = colNode->left; 

	// Move down the column and remove each row 
	// by traversing right 
	for(row = colNode->down; row != colNode; row = row->down) 
	{ 
		for(rightNode = row->right; rightNode != row; 
			rightNode = rightNode->right) 
		{ 
			rightNode->up->down = rightNode->down; 
			rightNode->down->up = rightNode->up; 

			// after unlinking row node, decrement the 
			// node count in column header 
			Matrix[0][rightNode->colID].nodeCount -= 1; 
		} 
	} 
} 

// Uncover the given node completely 
void uncover(struct Node *targetNode) 
{ 
	struct Node *rowNode, *leftNode; 

	// get the pointer to the header of column 
	// to which this node belong 
	struct Node *colNode = targetNode->column; 

	// Move down the column and link back 
	// each row by traversing left 
	for(rowNode = colNode->up; rowNode != colNode; rowNode = rowNode->up) 
	{ 
		for(leftNode = rowNode->left; leftNode != rowNode; 
			leftNode = leftNode->left) 
		{ 
			leftNode->up->down = leftNode; 
			leftNode->down->up = leftNode; 

			// after linking row node, increment the 
			// node count in column header 
			Matrix[0][leftNode->colID].nodeCount += 1; 
		} 
	} 

	// link the column header from it's neighbors 
	colNode->left->right = colNode; 
	colNode->right->left = colNode; 
} 

// Traverse column headers right and 
// return the column having minimum 
// node count 
Node *getMinColumn() 
{ 
	struct Node *h = header; 
	struct Node *min_col = h->right; 
	h = h->right->right; 
	do
	{ 
		if(h->nodeCount < min_col->nodeCount) 
		{ 
			min_col = h; 
		} 
		h = h->right; 
	}while(h != header); 

	return min_col; 
} 


void printSolutions() 
{ 
	cout<<"Printing Solutions: "; 
	vector<struct Node*>::iterator i; 

	for(i = solutions.begin(); i!=solutions.end(); i++) 
		cout<<(*i)->rowID<<" "; 
	cout<<"\n"; 
} 

// Search for exact covers 
void search(int k) 
{ 
	struct Node *rowNode; 
	struct Node *rightNode; 
	struct Node *leftNode; 
	struct Node *column; 

	// if no column left, then we must 
	// have found the solution 
	if(header->right == header) 
	{ 
		printSolutions(); 
		return; 
	} 

	// choose column deterministically 
	column = getMinColumn(); 

	// cover chosen column 
	cover(column); 

	for(rowNode = column->down; rowNode != column; 
		rowNode = rowNode->down ) 
	{ 
		solutions.push_back(rowNode); 

		for(rightNode = rowNode->right; rightNode != rowNode; 
			rightNode = rightNode->right) 
			cover(rightNode); 

		// move to level k+1 (recursively) 
		search(k+1); 

		// if solution in not possible, backtrack (uncover) 
		// and remove the selected row (set) from solution 
		solutions.pop_back(); 

		column = rowNode->column; 
		for(leftNode = rowNode->left; leftNode != rowNode; 
			leftNode = leftNode->left) 
			uncover(leftNode); 
	} 

	uncover(column); 
}


int main() 
{	 
	auto start = high_resolution_clock::now(); 
	/* 
	Example problem 

	X = {1,2,3,4,5,6,7} 
	set-1 = {1,4,7} 
	set-2 = {1,4} 
	set-3 = {4,5,7} 
	set-4 = {3,5,6} 
	set-5 = {2,3,6,7} 
	set-6 = {2,7} 
	set-7 = {1,4} 

	Solutions : {6 ,4, 2} and {6, 4, 7} 
	

	nRow = 6; 
	nCol = 7; 
	
	// initialize the problem matrix 
	// ( matrix of 0 and 1) with 0 
	for(int i=0; i<=nRow; i++) 
	{ 
		for(int j=0; j<nCol; j++) 
		{ 
			// if it's row 0, it consist of column 
			// headers. Initialize it with 1 
			if(i == 0) ProbMat[i][j] = true; 
			else ProbMat[i][j] = false; 
		} 
	} 

	// Manually filling up 1's 
	ProbMat[1][2] = true; ProbMat[2][0] = true; 
	ProbMat[1][4] = true; ProbMat[2][3] = true; 
	ProbMat[1][5] = true; ProbMat[2][6] = true;
	ProbMat[3][1] = true; ProbMat[3][2] = true;
	ProbMat[3][5] = true; ProbMat[4][0] = true;
	ProbMat[4][3] = true; ProbMat[5][1] = true;
	ProbMat[5][6] = true; ProbMat[6][3] = true;
	ProbMat[6][4] = true; ProbMat[6][6] = true;

	// create 4-way linked matrix 
	createToridolMatrix(); 
	search(0); 
	*/
	std::cout << "----------------------------------------------------------------" << std::endl;
	std::cout << " 2-(7,3,1) Design " << std::endl;
	constexpr auto solution = cmath::run_t_design<7, 3, 2>();
	cmath::print_solution<7, 3>(solution);
	std::cout << "----------------------------------------------------------------" << std::endl;
	std::cout << " 2-(15,3,1) Design " << std::endl;
	constexpr auto solution2 = cmath::run_t_design<15, 3, 2>();
	cmath::print_solution<15, 3>(solution2);
	std::cout << "----------------------------------------------------------------" << std::endl;
	std::cout << " There is no 2-(8,3,1) Design " << std::endl;
	std::cout << "----------------------------------------------------------------" << std::endl;
	constexpr auto solution3 = cmath::run_t_design<8, 3, 2>();
	cmath::print_solution<8, 3>(solution3);
	std::cout << "----------------------------------------------------------------" << std::endl;
	auto stop = high_resolution_clock::now();
	auto duration = duration_cast<microseconds>(stop - start);
	std::cout << "----------------------------------------------------------------" << std::endl; 
	std::cout << "Compile time: "<< duration.count() << "ms." << std::endl;
	return 0; 
} 

