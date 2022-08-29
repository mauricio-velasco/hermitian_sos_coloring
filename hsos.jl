using Base.Iterators
using DynamicPolynomials
using JuMP
using SCS
using LinearAlgebra
using IterTools

function reduce( p::AbstractPolynomialLike, d::Int)
    res = 0
    Vars = variables(p)
    num_vars = length(Vars)
    for term in terms(p)
        c = DynamicPolynomials.coefficient(term)
        exp_vector = exponents(monomial(term))
        reduced_exp_vector = [mod(j,d) for j in exp_vector] 
        new_monomial = prod([Vars[j]^reduced_exp_vector[j] for j in 1:num_vars])
        res += c * new_monomial
    end
    return res
end

function conjugate( p::AbstractPolynomialLike, d::Int)
    res = 0
    Vars = variables(p)
    num_vars = length(Vars)
    for term in terms(p)
        c = DynamicPolynomials.coefficient(term)
        exp_vector = exponents(monomial(term))
        reduced_exp_vector = [mod((-1)*j,d) for j in exp_vector] 
        new_c = conj(c)
        new_monomial = prod([Vars[j]^reduced_exp_vector[j] for j in 1:num_vars])
        res += new_c * new_monomial
    end
    return res
end


function build_proper3colored_edge_counting_poly(Edges, x)
    first = true
    target_poly = 0
    for edge in Edges
        i = edge[1]
        j = edge[2]
        term = x[i]*conjugate(x[j],3)+ x[j]*conjugate(x[i],3)
        summand = (2-term)/3
        if first == true
            first = false
            target_poly = summand
        else
            target_poly += summand
        end

    end
    return target_poly
end


function make_monomial(exponents_vector, x)
    @assert(length(exponents_vector) == length(x))
    new_monomial = prod([x[j]^exponents_vector[j] for j in eachindex(x)])
    return new_monomial
end


function new_diamond_basis_equal(t , x)
    if t==0 
        return [x[1]^0]
    else
        supports = IterTools.subsets(x,t)
        ss = [-1,1]
        result(ss, n) = Iterators.product(ntuple(i->ss, n)...)
        res = []        
        for support in supports
            for tuple_id in result(ss,length(support))
                exponents_vector = [x== -1 ? 2 : x for x in tuple_id]            
                new_monomial = prod([support[j]^exponents_vector[j] for j in 1:length(tuple_id)])
                push!(res,new_monomial)
            end        
        end
        return res

    end
end

function new_diamond_basis_at_most(t , x)
    res = []
    for k in 0:t
        append!(res, new_diamond_basis_equal(k,x))
    end
    return res
end


function build_diamond_bases(multiplier_degree_t, x)
    Dg = new_diamond_basis_at_most(multiplier_degree_t,x)
    Dh = new_diamond_basis_at_most(multiplier_degree_t + 1,x)
    return Dg, Dh
end


function new_build_SDP(target_f,Dg,Dh,x,model)
    Dgbar = Vector{Any}(map((x)->conjugate(x,3), Dg))
    Dhbar = Vector{Any}(map((x)->conjugate(x,3), Dh))
    #Hermitian matrices are declared by comparing real and imaginary parts
    m =length(Dg)
    @variable(model, A1[1:m,1:m] in SymmetricMatrixSpace()) 
    @variable(model, B1[1:m,1:m] in SkewSymmetricMatrixSpace()) 
    n = length(Dh)
    @variable(model, A2[1:n,1:n] in SymmetricMatrixSpace()) 
    @variable(model, B2[1:n,1:n] in SkewSymmetricMatrixSpace()) 
    print("Model with hermitian matrices of sizes $m and $n.\n")
    print("Writing linear restrictions...\n")

    print("Computing reductions of quadratic forms...\n")
    R1 = reduce(transpose(Dgbar) * A1 *Dg,3)
    R2 = reduce(transpose(Dhbar) * A2* Dh, 3)
    print("Computing reduction of multiples of real part of fg-h...\n")
    real_part_difference = reduce(target_f*R1-R2,3) 

    linears1 = DynamicPolynomials.coefficients(real_part_difference)
    for term in linears1
        @constraint(model, term == 0)
    end
    #Imaginary_equalities
    print("Computing reductions of quadratic forms...\n")
    T1 = reduce(transpose(Dgbar) * B1*Dg,3)
    T2 = reduce(transpose(Dhbar) * B2*Dh, 3)
    print("Computing reduction of multiples of imaginary part of fg-h...\n")
    im_part_difference = reduce(target_f*T1-T2 ,3)

    linears2 = DynamicPolynomials.coefficients(im_part_difference)
    for term in linears2
        @constraint(model, term == 0)
    end
    #Nontriviality constraints
    @constraint(model, tr(A1) == 1)

    print("Writing semidefinite constraints...\n")
    C1 = vcat(hcat(A1,B1),hcat(transpose(B1), A1))
    @constraint(model, C1 >= 0, PSDCone())
    C2 = vcat(hcat(A2,B2),hcat(transpose(B2), A2))
    @constraint(model, C2 >= 0, PSDCone())
end


function new_is_edge_quantity_UB_3colored_edges(edge_quantity_ub, diamond_degree_t, num_graph_vertices, graph_edges)
    num_vertices = num_graph_vertices
    Edges = graph_edges
    model = Model(SCS.Optimizer)
    print("Computing objective polynomial...\n")
    @polyvar x[1:num_vertices]
    f = build_proper3colored_edge_counting_poly(Edges, x)
    multiplier_degree_t = diamond_degree_t
    Dg, Dh = build_diamond_bases(multiplier_degree_t, x)
    target_f = edge_quantity_ub - f
    print("Building restrictions...\n")
    new_build_SDP(target_f,Dg,Dh,x,model)
    print("Model construction terminated. Optimizing...\n")
    optimize!(model)
    return termination_status(model), model
end


#EXAMPLE

#Initial graph: 4-cycle
num_vertices = 4
Edges = [[1,2],[2,3],[3,4],[4,1]]
Edges = [[1,2],[1,3],[1,4],[2,3], [2,4],[3,4]]

@polyvar x[1:num_vertices]
f = build_proper3colored_edge_counting_poly(Edges, x)
#Time the reduction
Dg, Dh = build_diamond_bases(1,x)
model = Model(SCS.Optimizer)
print("Computing objective polynomial...\n")


#MINI TEST:
status, model = new_is_edge_quantity_UB_3colored_edges(5,2,num_vertices,Edges)#should be feasible
status, model = new_is_edge_quantity_UB_3colored_edges(2,3,num_vertices,Edges)#should be infeasible
#Look at the obtained solutions...
value(model[:A1])


#General complete graph
num_vertices = 10
Edges = [tuple for tuple in IterTools.subsets(1:num_vertices,2)]
status, model = new_is_edge_quantity_UB_3colored_edges(length(Edges)-1,1,num_vertices,Edges)#is feasible
status, model = new_is_edge_quantity_UB_3colored_edges(length(Edges)-2,1,num_vertices,Edges)#should be feasible

#Special 8 vertex graph:
num_vertices = 8
Edges = [[1,2], [2,3], [3,4], [4,5], [5,6], [6,7], [8,1], [8,2], [2,4], [4,6], [6,8]]
status, model = new_is_edge_quantity_UB_3colored_edges(length(Edges)-1,1,num_vertices,Edges)#infeasible
status, model = new_is_edge_quantity_UB_3colored_edges(length(Edges)-1,2,num_vertices,Edges)#infeasible
