#
#   hleaps based on Doug Bates's approach and some of his code
#
#   Author: Mark Banghart
#
#   examples of calls
#       out <- hleaps(y~x1+x2+x3+x1:x2+x2:x3, criteria="R2",
#                     traceModels=TRUE, altOut=TRUE)
#
#       out2 <- hleaps(y~x1+x2+x3+x4+x5+x6+(x1+x2+x3+x4+x5+x6)^2, data=data2,
#                    nBest=5, minSize=2, maxSize=6, timeOut=300)
#
#   Issues to be completed    
#       - Test when a column (but not a term) is NA 
#       - support models with no intercept or block dropping the intercept
#       - profile code to optimize the search loop
#       - limit search to only model sizes that are in the min to max range
#       - Apply a bounded algorithm based on SSMod values
#       - consider other indicators besides order (a 1:n ordering) like percentile
#
#
######################################################################

hleaps <- function (formula, 
                    data, 
                    subset, 
                    weights, 
                    na.action, 
                    offset, 
                    criteria="adjR2",   # critria to be reported
                    nBest=3,            # number of best models per size
                    minSize=NULL,       # smallest size of model reported
                    maxSize=NULL,       # largest size of model reported
                    timeOut=NULL,       # number of seconds to search for models
                    traceModels=FALSE,  # display all models checked as best
                    altOut=FALSE,       # alternate display for output
                    greedy=FALSE,       # use greedy search (slower but dirrected)
                    ...) {

#   Calculates Sum of Squares of the Models in a setId subset
#
calcSSMod <- function (setId) {

    set <- sets[[setId]]
    nSet <- nrow(set)

    #  Create the list of columns needed for largest model of subset
    #
    mod <- set[nSet,]
    i.cols  <- colAssign %in% c(0, which(mod))  # 0 is for intercept 

    # select the columns from the R matrix and calculate column effects 
    #
    ared  <- colAssign[i.cols]
    this.R <- R[,i.cols]
    QR <- qr(this.R)
    SS.R <- qr.qty(QR,eff)[1:length(i.cols)]
    num.sets <<- num.sets + 1


        # Try both ways of constructing sum of squares
        #
#        this.X <- X[,i.cols]
#        QR <- qr(this.X)
#        SS.X <- qr.qty(QR,resp.vec)[1:length(i.cols)]


    #  Calculate the SSModel for each model in the subset
    #
    SSCol <- SS.R^2  
    j.SSMod <- SSCol[1]  # include SS for intercept
    prior.mod <- rep(FALSE,num.terms)
    for (j in rownames(set)) {     # (j in 1:nSet) {
        j.newTerms <- which(xor(prior.mod,(i.terms <- set[j,])))
        if (length(j.newTerms) > 0)
            {
            j.cols <- SSCol[which(ared %in% j.newTerms)]
            j.SSMod <- j.SSMod + sum(j.cols)
            }
        SSMod[j] <<- j.SSMod   
        sizeMod[j] <<- sum(set[j,])
        prior.mod <- i.terms
        }

        #  TEMPORARY TEST CODE
        #  Calculate the SSModel for each model in the subset
        #
#        i.SSCol <- SS.X^2  # for testing with full X columns SS.X^2
#        j.SSMod <- i.SSCol[1]  # include SS for intercept
#        prior.mod <- rep(FALSE,num.terms)
#        for (j in 1:nSet)
#            {
#            j.newCol <- which(xor(prior.mod,set[j,]))
#            if (length(j.newCol) > 0)
#                {
#                j.SSMod <- j.SSMod + sum(i.SSCol[which(ared %in% j.newCol)])
#                }
#            SSmodX[rownames(set)[j]] <<- j.SSMod   
#            prior.mod <- set[j,]
#            }
    }


##########################################################################
#
#   FindBest recursively calls it self with the most significant term dropped and forced
#       The most significant term is found by calculating the subset models of all free terms
#
findBest <- function (this.terms, this.forced, forced=FALSE, forced.freeSS) {

    this.pred <- c(this.terms, this.forced)
    if ( length(this.pred) <= 0) return()  # bad call if no predictors in the model

    if (!forced) {
        if (traceModels) {   # traceModels displays each model that is passed to findBest
            num.models <<- num.models + 1
            message("Check: ", format(num.models,trim = FALSE,width=4), 
#                    " RSS: ", format(this.RSS,trim = FALSE,width=8,digits=7), 
                    "  ", format(length(this.pred),trim = FALSE,width=2), 
                    "  terms: ", paste(c(this.terms),collapse=", "), 
                    " - - forced terms: ", paste(c(this.forced),collapse=", "))
            }

        #   Find the list of terms that are free to be dropped
        #
        this.incidencef <- incidencef[,this.pred]
        if (length(this.terms) > 1) {
            zero.rows <- (rowSums(this.incidencef) == 0)
            zero.terms <- terms[zero.rows]
            free <- zero.terms[(terms[zero.rows] %in% this.terms)]
        } else {
            free <- this.terms
            }
        if (length(free)==0) return()  # no terms to drop or force


        #   Find the SSModel for each sub-model with a single free term dropped
        #
        freeSS <-c(0)[-1]
        for (i in free) {
            #   find the model id for the model with the dropped free term
            #
            i.pred <- (terms %in% this.pred[which(this.pred != i)])
            i.modName <- paste(c("m",as.integer(i.pred)),collapse="")
            i.modId <- modId[i.modName]      
 
            #   if no SSMod for this model, calculate the SSMod for the subset which included it
            #
            if (SSMod[i.modId] < 0) calcSSMod(setIds[i.modId])

            #   add to the list of SSMods for the free terms
            i.mod <- SSMod[i.modId]
            names(i.mod) <- i
           freeSS <- c(freeSS,i.mod)
           }  
    } else {   #  if forced, used the SSModels calculated at the above level
        freeSS <- forced.freeSS
        }
  
    this.time <- proc.time()
    if ( (this.time - start.time)[3] > timeOut) {  # over timeOut time?
        if (outOfTime == FALSE) {
            message ("Warning - processing time exceeded ", timeOut, 
                     " partial results have been returned")
            }
        outOfTime <<- TRUE
        return()
        }

    if (length(freeSS)==0) return()  # no terms to drop or force

    #   find the best model of the set of dropped free terms
    #          
    signf.free <- names(which( freeSS == min(freeSS))[1] ) # least significant

    #   If there are terms after dropping, continue dropping & forcing terms
    #
    new.terms <- this.terms[-which(this.terms==signf.free)]   
    if ( length(new.terms) >= 1 ) {   # are there terms to drop or force?
        findBest(new.terms, this.forced)    # drop the term
        #    force the least significant term into the model
        new.forced <- c(this.forced, signf.free)
        new.freeSS <- freeSS[-which(names(freeSS)==signf.free)]
        findBest(new.terms, new.forced, forced=TRUE, forced.freeSS=new.freeSS)     # force the term
        }

    }



###########################################################################
#
#   FindBest2 search the subset list in order.
#
findBest2 <- function (this.terms, this.forced) {

    #   Find the SSModel for each sub-model with a single free term dropped
    #
    for (i in 1:s) {
        calcSSMod(i)
        begin_lm_time <- proc.time()
        if ( (begin_lm_time - start.time)[3] > timeOut) {  # over timeOut time?
            message ("Warning - processing time exceeded ", timeOut, 
                     " partial results have been returned")
            return()
            }
        }   
    }





###########################################################################
#
#   FindBest2p profile the search of the subset list in order.
#
#      Used only to test the efficency of the code.  Not used in final version
#
findBest2p <- function (this.terms, this.forced) {

    #   Find the SSModel for each sub-model with a single free term dropped
    #
    Rprof("findBest2.out")
    for (i in 1:s) {

    set <- sets[[i]]
    nSet <- nrow(set)

    #  Create the list of columns needed for largest model of subset
    #
    mod <- set[nSet,]
    i.cols  <- colAssign %in% c(0, which(mod))  # 0 is for intercept 

    # select the columns from the R matrix and calculate column effects 
    #
    ared  <- colAssign[i.cols]
    this.R <- R[,i.cols]
    QR <- qr(this.R)
    SS.R <- qr.qty(QR,eff)[1:length(i.cols)]
    num.sets <<- num.sets + 1

    #  Calculate the SSModel for each model in the subset
    #
    SSCol <- SS.R^2  
    j.SSMod <- SSCol[1]  # include SS for intercept
    prior.mod <- rep(FALSE,num.terms)
    for (j in rownames(set)) {     # (j in 1:nSet) {
        j.newTerms <- which(xor(prior.mod,(i.terms <- set[j,])))
        if (length(j.newTerms) > 0)
            {
            j.cols <- SSCol[which(ared %in% j.newTerms)]
            j.SSMod <- j.SSMod + sum(j.cols)
            }
        SSMod[j] <<- j.SSMod   
        sizeMod[j] <<- sum(set[j,])
        prior.mod <- i.terms
        }
        }   
    Rprof(NULL)
    }


###########################################################################
#
#   format the compressed which matrix of subsets
#

format.subsets <- function (sdf) {
	
    num.row <- nrow(sdf)
    num.col <- ncol(sdf)
    num.d.col <- num.col%/%5
    if (num.col%%5 > 0) num.d.col <- num.d.col + 1
	
    sd <- data.frame(c(1:num.row))[,-1]  # create an empty data frame
    row <- 1
    while (row <= num.row) {
        col <- 1
        d.col <- 1
        while (col <= num.col) {
            if (col+4 < num.col) {
			end.col <- col+4
            } else {
                end.col <- num.col
                }
            sd[row,d.col] <- paste(paste(ifelse(sdf[row,col:end.col]==TRUE,"T",".")), collapse= "")
            col <- col+5
            d.col <- d.col+1
            }
        row <- row + 1
        }

    # Create column names
    #
    col <- 1
    d.col <- 1
    sd.names <- c(1)
    while (col <= num.col) {
        if (col+4 < num.col) {
            end.col <- col+4
        } else {
            end.col <- num.col
        }
        this.name <- c(seq(col+1,end.col))
        this.index <- this.name[1]%/%10
        this.name <- this.name%%10
        sd.names[d.col] <- paste(col,end.col,sep="-")
        col <- col+5
        d.col <- d.col+1
        }

    names(sd) <- sd.names
    sd
    }


###########################################################################
#
#
#   format the output
#
format.output <- function() {

    #   Order the models based on size of model and SSResid
    #       Then select nBest models of each size
    #
    SSResid <- SSTotal - SSMod
    mod.order <- order(sizeMod, SSResid)  
    results <- data.frame(size=sizeMod[mod.order], 
                          SSResid=SSResid[mod.order], SSModel=SSMod[mod.order],
                          SSMod_X=SSmodX[mod.order])

    #   Remove models that are not in the best nBest for each size
    #
    all <- results
    for (i in 0:num.terms) {
        size.lst <- which(results[,"size"] %in% i)
        if (i < minSize) {
            results <- results[-size.lst,]
            }
        else if (i > maxSize) {
            results <- results[-size.lst,]
            }
        else if (length(size.lst) > nBest) 
            {
            to.del <- size.lst[-c(1:nBest)]
            results <- results[-to.del,]
            }
        }
    size <- results[,"size"]
    SSRes <- results[,"SSResid"]
    SSMod <- results[,"SSModel"]

    dfMod <- rep(0,nrow(results))
    modTerms <- matrix(ncol=num.terms, nrow=nrow(results))
    colnames(modTerms) <- colnames(mods)
    rownames(modTerms) <- rownames(results)
    for (i in 1:nrow(results)) {
        i.cols  <- colAssign %in% c(0, which(mods[rownames(results)[i],]))  # 0 is for intercept 
        dfMod[i] <- sum(as.integer(i.cols))
        modTerms[i,] <- mods[rownames(results)[i],]
        }

    Moddf <- dfMod
    otherCol <- c("size","SSResid","SSModel","SSMod_X")
    terms.matrix <- modTerms
    mod.order <- order(SSRes)  

    RSq <- (SSMod-SSIntercept) / (SSRes+SSMod)
    adjRSq <- 1 - (1 - RSq)*((dfTotal - 1)/(dfTotal-Moddf)) # correct if no intercept
 
    if (!altOut) {  # if normal output format

        #   Check the critera used
        #
        if (criteria=="R2") {
            BSS <- list(which=terms.matrix, label=colnames(mods), 
                        size=results[,"size"], Rsquared=RSq)   
        } else if(criteria=="adjR2"){
            BSS <- list(which=terms.matrix, label=colnames(mods), 
                        size=results[,"size"], adjRsqrd=adjRSq)  
        } else { 
            BSS <- list(which=terms.matrix, label=colnames(mods), 
                        size=results[,"size"], rss=SSRes)   
            } 

    } else {   # otherwise alternate formated output

        #   compress the which matrix
        #
        comp.mod <- format.subsets(terms.matrix)

        # formate execution info
        #
        total.time <- proc.time()[3] - start.time[3]
        time.usage <- paste("Total number of model subsets examined was ", num.sets,
                            " Total run time was ", 
                            format(total.time,trim = FALSE,digits=7), " seconds.")
        if (criteria=="R2") {
            modelInfo <- cbind(size, order=mod.order, RSq, 
                               comp.mod)   
        } else if(criteria=="adjR2"){
            modelInfo <- cbind(size, order=mod.order, adjRSq, 
                               comp.mod)  
        } else { 
            modelInfo <- cbind(size, order=mod.order, SSRes, 
                               comp.mod)     
            } 
        BSS <- list(modelInfo=modelInfo, label=colnames(mods),executionInfo=time.usage)
        }

    }

##################################################################################
#
#   hleaps code starts here
#
##################################################################################

    #   Parms handling
    #
    cl   <- match.call()
    mf   <- match.call(expand.dots = FALSE)
    m    <- match(c("formula", "data", "subset", "weights", "na.action", 
                    "offset"), names(mf), 0L)
    mf   <- mf[c(1L, m)]
    mf$drop.unused.levels <- TRUE

    #   use lm to determine if there are terms that are not needed (NA coefficients)
    #
    formula <- as.formula(formula)  # coerce formula
    if (missing(data)) {
        lm.out <- lm(formula)
    } else {
        lm.out <- lm(formula, data=data)
        }
    terms <- attr(lm.out$terms,"term.labels")
    na.col <- is.na(lm.out$coefficients)
    colAssign <- lm.out$assign
    needed.terms <- c("")[-1]
    for (i in 1:length(terms)) {
        if (!as.logical(prod(na.col[which(colAssign == i)]))) 
            needed.terms <- c(needed.terms, terms[i])
        }
    resp <- as.character(formula[2])
    new.formula <- as.formula(paste(resp,"~", paste(needed.terms, collapse= "+"),sep=""))
    num.terms <- length(needed.terms)

    #   use lm to determine if there are columns that are not needed (NA columns)
    #
    if (missing(data)) {
        lm.out <- lm(new.formula)
    } else {
        lm.out <- lm(new.formula, data=data)
        }
    na.cols <- which(is.na(lm.out$coefficients))

    #   Check parameters and set default if needed
    #
    if (is.null(minSize)) minSize <- 1 
    if (is.null(maxSize)) maxSize <- num.terms
    if (is.null(timeOut)) timeOut=Inf

    if (minSize >= num.terms) { 
        message ("Error - minSize must be less than number of terms - instead of "
                  , minSize)
        minSize <- 1
        }
    if (minSize < 1) { 
        message ("Error - minSize must be at least 1 - instead of "
                  , minSize)
        minSize <- 1
        }
    if (maxSize < minSize) { 
        message ("Error - maxSize must be at least as large as minSize - instead of "
                  , maxSize)
        maxSize <- num.terms
        }
    if (!(criteria %in% c("adjR2","R2","RSS"))) {
        message ("Error - criteria must me adjR2, R2, or RSS - instead of "
                  , criteria)   
        criteria <- "adjR2"
        }
    if (nBest<1) {
        message ("Error - nBest must be greater than 0 - instead of "
                  , nBest)   
        nBest <- 3
        }    
    if (!(is.logical(traceModels))) {
        message ("Error - traceModels must be logical - instead of "
                  , traceModels)   
        traceModels=FALSE
        }
    if (!(is.logical(altOut))) {
        message ("Error - altOut must be logical - instead of "
                  , altOut)   
        altOut=FALSE
        }
    if (!(is.logical(greedy))) {
        message ("Error - greedy must be logical - instead of "
                  , greedy)   
        greedy=FALSE
        }

    #  Create list of models and grouped subsets of models using Doug Bates's code
    #    And get the needed data
    #
    if (missing(data)) {
        hp    <- hpmods(new.formula, ...)
    } else {
        hp <- hpmods(new.formula, data=data, ...)
        }
    mods  <- hp$models
    n <- nrow(mods)
    num.terms <- ncol(mods)
    X     <- hp$X
    dfTotal <- nrow(X)
    incidence <- hp$incidence
    terms <- attr(attr(hp$frame,"terms"),"term.labels")
    term.order <- attr(attr(hp$frame,"terms"),"order")
    names(term.order) <- terms

    sets  <- msubs(hp, fr)
    s <- length(sets)

    #   incident table used to find free terms
    #
    max.order <- max(term.order)    
    incidencef <- incidence
    for (i in terms) {
        i.order <- term.order[i]
        incidencef[(term.order %in% i.order:max.order),i] <-0
        }

    #   name models based on the terms in the model
    #
    mod.names = c("")
    nmods <- mods
    for (i in 1:nrow(nmods)) {
        mod.names[i] <- paste(c("m",as.integer(mods[i,])),collapse="") 
        }
    modId <- rownames(mods)
    names(modId) <- mod.names

    #   create vector to translate from a model to subset index
    #
    setIds <- mods[,1]
    for (i in 1:s) {        
        i.set <- sets[[i]]
        nSet <- nrow(i.set)
        for (j in 1:nSet) {
            setIds[rownames(i.set)[j]] <- i
            }
        }    

    #   create the R matrix for total model
    #
    if (length(na.cols) != 0) {
        new.X <- X[,-na.cols]   # removed columns that lm returns as NAs
    } else {
        new.X <- X
        }
    QR <- qr(new.X)         # preform decomposition on remaining columns
    R <- qr.R(QR)
    resp.vec <- model.response(hp$frame)
    eff.list <- qr.qty(QR,resp.vec)
    eff <- eff.list[1:ncol(X)]
    SSTotal <- sum(eff.list^2)
    SSIntercept <- eff[1]^2
    SSTotCM <- sum((eff.list-mean(eff.list))^2)
    SSIntercept <- eff.list[1]^2
    colAssign <- attr(X,"assign")

    #   tables to record the Sum of Squares, size, Terms and df for each model
    #
    SSMod <- rep(-1,n)
    names(SSMod) <- rownames(mods)
    sizeMod <- rep(0,n)
    names(sizeMod) <- rownames(mods)
    modTerms <- matrix(nrow=n, ncol=num.terms)
    rownames(modTerms) <- rownames(mods)
    dfMod <- rep(0,n)
    names(dfMod) <- rownames(mods)
    SSmodX <- rep(0,n)
    names(SSmodX) <- rownames(mods)

    #   search for the best subset of models
    #
    num.models <- 0
    num.sets <- 0
    start.time <- proc.time()
    outOfTime <- FALSE

    forced.terms <- c("")[-1]
    if (greedy) {
        findBest(needed.terms, forced.terms)
    } else {
        findBest2(needed.terms, forced.terms)
        }

    format.output()
    }                   #   End of hleaps




