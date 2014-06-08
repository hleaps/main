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

##  hpmodsetup 
##
##  Does all of what hpmods does except create the matrix of models
##
##  Modified from Doug Bates hpmods function
##  documentation for which is below
##
##' Determine hierarchy-preserving models
##'
##' Determine the hierarchy-preserving models from a formula
##' @title Hierarchy-preserving models
##' @param formula as in \code{"\link{lm}"}
##' @param data as in \code{"\link{lm}"}
##' @param subset as in \code{"\link{lm}"}
##' @param weights as in \code{"\link{lm}"}
##' @param na.action as in \code{"\link{lm}"}
##' @param offset as in \code{"\link{lm}"}
##' @param \dots optional, additional arguments.  At present, none are used.
##' @return an object of class \code{"hpmods"}
##' @author Douglas Bates
##' @keywords models
##' @examples
##' set.seed(12321)
##' fr <- data.frame(y = rnorm(900), x1 = rnorm(900), x2 = rnorm(900),
##'                  x3 = gl(3,10,900), x4 = gl(10,3,900))
##' (hpm <- hpmods(y ~ (x1 + x2 + x3 + x4)^4, fr))
##' @export
hpmodsetup <- function(formula, data, subset, weights, na.action, offset, ...) {
    cl   <- match.call()
    mf   <- match.call(expand.dots = FALSE)
    m    <- match(c("formula", "data", "subset", "weights", "na.action", 
                    "offset"), names(mf), 0L)
    mf   <- mf[c(1L, m)]
    mf$drop.unused.levels <- TRUE
    mf[[1L]] <- as.name("model.frame")
    mf   <- eval(mf, parent.frame())
    atts <- attributes(terms(mf))
    inci <- crossprod(atts$factor) == atts$order # incidence matrix for terms
    mods <<- array(FALSE, c(nrow(inci), 1))
    rownames(mods) <<- rownames(inci)
    mods <<- t(mods)
    rownames(mods) <<- mods %*% 2^((seq_len(ncol(inci)))-1)
    res  <<- list(call=cl, incidence=inci, models=mods,
                 frame=mf, X=model.matrix(terms(mf), mf))
    class(res) <<- "hpmods"
    res
}


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
                    timeOut=NULL,       # number of seconds to search 
                                        #  for models
                    traceModels=FALSE,  # display all models checked as best
                    altOut=FALSE,       # alternate display for output
                    greedy=FALSE,       # use greedy search (slower but
                                        #  dirrected)
                    largeMem=FALSE,     # True if computer has large amount
                                        # of memory
                    ...) {



##################################################################################
#
#   hleaps code starts here
#
##################################################################################
 
    #   initial parmeter handling
    #
    cl   <- match.call()
    mf   <- match.call(expand.dots = FALSE)
    m    <- match(c("formula", "data", "subset", "weights", "na.action", 
                    "offset"), names(mf), 0L)
    mf   <- mf[c(1L, m)]
    mf$drop.unused.levels <- TRUE


    #   use lm to determine the number of terms
    #
    formula <- as.formula(formula)  # coerce formula
    if (missing(data)) {
        lm.out <- lm(formula)
    } else {
        lm.out <- lm(formula, data=data)
        }
    terms <- attr(lm.out$terms,"term.labels")
  #  termList <- terms
    num.terms <<- length(terms)

    #   Check that the number of terms is 30 or lower
    #   This prevents the size of matrix built by hpmods
    #   from being too big.
    #
    maxTerms <- 30
    if (num.terms > maxTerms) {
        message ("Error - maximum number of terms must be less than 30 - instead of "
                  , num.terms)
        terms <- terms[1:maxTerms]
        num.terms <- maxTerms 
        new.formula <- as.formula(paste(as.character(formula[2]),"~", 
                                  paste(terms, collapse= "+"),
                                  sep=""))
    } else {
        new.formula <- formula
        }

    #   Check parameters and set defaults as needed
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

    message ("Parameters checked")

    #  Create list of models and grouped subsets of models using 
    #   Doug Bates's code     And get the needed data
    #
    new.formula <- as.formula(formula)  # coerce formula
    if (missing(data)) {
        hp    <- hpmodsetup(new.formula, ...)
    } else {
        hp <- hpmodsetup(new.formula, data=data, ...)
        }
    mods  <- hp$models
    X     <<- hp$X
    dfTotal <<- nrow(X)

    # set up incidence matrix and initialize terms list
    incidence <- hp$incidence
    termLabels <- attr(attr(hp$frame,"terms"),"term.labels")
    terms <- seq(1,length(termLabels))
    term.order <- attr(attr(hp$frame,"terms"),"order")
    names(term.order) <- terms
    resp.vec <<- model.response(hp$frame)

    #   Decomposition of full model
    #
    QR <- qr(X)
    eff.list <- qr.qty(QR,resp.vec)
    SSIntercept <<- eff.list[1]^2
    SSTotal <<- sum(eff.list^2)
    colAssign <<- attr(X,"assign")

    message ("QR for total model complete")


    #   tables to record the Sum of Squares, size, Terms and df for each model
    #
    maxMods <- 2^(num.terms)
    SSMod <<- rep(-1,maxMods)
    sizeMod <<- rep(0,maxMods)
    dfMod <- rep(0,maxMods)

    #   search models by subsets for best models
    #
    num.models <<- 0
    num.sets <<- 0
    start.time <<- proc.time()
    outOfTime <<- FALSE

    message ("setup done")


    if (greedy) {
        #   incident table used to find free terms
        #
        max.order <- max(term.order)    
        notFree <- incidence
        rownames(notFree) <- terms
        colnames(notFree) <- terms
        for (i in terms) {
            i.order <- term.order[i]
            notFree[(term.order %in% i.order:max.order),i] <-0
            }

        forced.terms <- c("")[-1]
        needed.terms <- terms

        calcSSModGred(needed.terms)   # calc SS for all model

        findBest(needed.terms, forced.terms, traceModels=traceModels, terms=terms, notFree=notFree, timeOut=timeOut)

    } else {

        #  Create list of models and grouped subsets of models using 
        #   Doug Bates's code     And get the needed data
        #
        new.formula <- as.formula(formula)  # coerce formula
        if (missing(data)) {
            hp    <- hpmods(new.formula, ...)
        } else {
            hp <- hpmods(new.formula, data=data, ...)
        }
        mods  <- hp$models

        sets  <- msubs(hp, fr)
        s <- length(sets)

        findBest2(s = s, sets = sets, timeOut = timeOut)
        }

    format.output(minSize, maxSize, nBest, altOut, criteria)
    }                   #   End of hleaps


#   Calculates Sum of Squares of the Models in a setId subset
#
calcSSMod <- function (setId, sets) {
  
  set <- sets[[setId]]
  nSet <- nrow(set)

  #  Create the list of columns needed for largest model of subset
  #
  mod <- set[nSet,]
  i.cols  <- colAssign %in% c(0, which(mod))  # 0 is for intercept 
  
  # select the columns from the R matrix and calculate column effects 
  #
  ared  <- colAssign[i.cols]
  this.X <- X[,i.cols]
  QR <- qr(this.X)
  SS.X <- qr.qty(QR,resp.vec)[1:length(i.cols)]
  num.sets <<- num.sets + 1
  
  
  #  Calculate the SSModel for each model in the subset
  #
  SSCol <- SS.X^2  
  j.SSMod <- SSCol[1]  # include SS for intercept
  prior.mod <- rep(FALSE,num.terms)
  for (j in rownames(set)) {     # (j in 1:nSet) {
    j.newTerms <- which(xor(prior.mod,(i.terms <- set[j,])))
    if (length(j.newTerms) > 0)
    {
      j.cols <- SSCol[which(ared %in% j.newTerms)]
      j.SSMod <- j.SSMod + sum(j.cols)
    }
    j.modIdx <- as.integer(j)
    SSMod[j.modIdx] <<- j.SSMod   
    sizeMod[j.modIdx] <<- sum(set[j,])
    prior.mod <- i.terms
  }
}


###########################################################################
#
#   FindBest2 search the subset list in order.
#
findBest2 <- function (s, sets, timeOut) {
  
  #   Find the SSModel for each sub-model with a single free term dropped
  #
  for (i in 1:s) {
    calcSSMod(i, sets)
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
#   format the compressed which matrix of subsets. Used to format
#   alternative output.
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
      # alt out formatting for mods
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
#   format the output
#
format.output <- function(minSize, maxSize, nBest, altOut, criteria) {
  
  #   Order the models based on size of model and SSResid
  #       Then select nBest models of each size
  #
  SSResid <- SSTotal - SSMod
  mod.order <- order(sizeMod, SSResid)  
  results <- data.frame(size=sizeMod[mod.order], 
                        SSResid=SSResid[mod.order], 
                        SSModel=SSMod[mod.order],
                        modId=mod.order 
  )
  
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
  SSMod <<- results[,"SSModel"]
  modId <- results[,"modId"]
  
  #   Code to convert index to terms (binary) 
  #
  decId <- modId
  modTerms <- matrix(ncol=num.terms, nrow=nrow(results))
  for (i in num.terms:1) {    
    modTerms[,i] <- decId >= 2^(i-1)
    decId <- decId - ifelse(modTerms[,i],2^(i-1),0)
  }
  
  dfMod <- rep(0,nrow(results))
  for (i in 1:nrow(results)) {
    # 0 is for intercept 
    i.cols  <- colAssign %in% c(0, modTerms[i,])
    dfMod[i] <- sum(as.integer(i.cols))
  }
  
  Moddf <- dfMod
  otherCol <- c("size","SSResid","SSModel")
  terms.matrix <- modTerms
  mod.order <- order(SSRes)  
  
  RSq <- (SSMod-SSIntercept) / (SSRes+SSMod)
  
  # correct if no intercept
  adjRSq <- 1 - (1 - RSq)*((dfTotal - 1)/(dfTotal-Moddf))
  
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
    time.usage <- paste("Total number of model subsets examined was ",
                        num.sets,
                        " Total run time was ", 
                        format(total.time,trim = FALSE,digits=7), 
                        " seconds.")
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
    BSS <- list(modelInfo=modelInfo, label=colnames(mods),
                executionInfo=time.usage)
  }
}


#   Used for the greedy search algorithm
#   Calculates sum of squares for all the possible nested models  
#       within the current set of terms.  It may recalculate the
#       sum of squares for nested models.
#   The terms must be provided in the sorted with the lowest ordered
#       terms first to the highet ordered terms
#
calcSSModGred <- function (
  terms                # vector of id numbers for terms in model
) {
  
  #  Create the list of columns needed for largest model
  #
  i.cols  <- colAssign %in% c(0, terms)  # 0 is for intercept 
  
  # select the columns from the X matrix and calculate column effects 
  #
  ared  <- colAssign[i.cols]   # column assignments for this model
  this.X <- X[,i.cols]
  QR <- qr(this.X)
  SS.X <- qr.qty(QR,resp.vec)[1:length(i.cols)]
  #    num.sets <<- num.sets + 1
  
  #  Calculate the SSModel for each model in the subset
  #
  SSCol <- SS.X^2  
  j.SSMod <- SSCol[1]            # include SS for intercept
  termIds <- terms
  nSet <- length(terms)
  
  #    error("debug stop in SSMods")
  
  for (j in 1:nSet) {         # for each term of terms
    j.term <- termIds[j]
    # which columns to sum for this term
    j.cols <- SSCol[which(ared %in% j.term)]  
    # cumulative sum for terms so far 
    j.SSMod <- j.SSMod + sum(j.cols)
    #
    i.modIdx <- sum(2^(terms[1:j]-1))
    SSMod[i.modIdx] <<- j.SSMod        
    sizeMod[i.modIdx] <<- j      # number of terms in model
  }
  
}


##########################################################################
#
#   FindBest recursively calls it self with the most significant term dropped and forced
#       The most significant term is found by calculating the subset models of all free terms
#
findBest <- function (this.terms,   # ordered list of terms in model 
                      this.forced,  # list of terms forced into model
                      forced=FALSE, # Indicator for forced call
                      forced.freeSS, # list of SS for free terms if force
                      traceModels,
                      terms,
                      notFree,
                      timeOut
) {
  
  if ( length(this.terms) <= 0) return()  # bad call if no predictors
  # in the model
  if (!forced) {
    if (traceModels) {   # traceModels displays each model that is passed to findBest
      num.models <<- num.models + 1
      message("Check: ", format(num.models,trim = FALSE,width=4), 
              #                    " RSS: ", format(this.RSS,trim = FALSE,width=8,digits=7), 
              "  ", format(length(this.terms),trim = FALSE,width=2), 
              "  terms: ", paste(c(this.terms),collapse=", "), 
              " - - forced terms: ", paste(c(this.forced),collapse=", "))
    }
    
    #   Find the list of terms that are free to be dropped
    #
    # 
    #  the following line is not to be checked
    #
    this.noForce <- setdiff(this.terms,this.forced)
    if (length(this.terms) > 1) {
      this.notFree <- notFree[,this.terms]
      free.rows <- (rowSums(this.notFree) == 0)
      this.free <- terms[free.rows]
      free <- this.free[(this.free %in% this.noForce)]
    } else {
      free <- this.terms
    }
    if (length(free)==0) return()  # no terms to drop or force
    
    #   Find the SSModel for each sub-model with a single 
    #   free term dropped
    #
    freeSS <-c(0)[-1]
    if (length(this.terms)>1) {
      for (i in free) {
        #   find the model id for the model with the dropped
        #   free term
        #
        i.terms <- this.terms[this.terms != i]
        i.modIdx <- sum(2^(i.terms-1))
        #
        #   if no SSMod for this model, calculate the SSMod for the subset which included it
        #
        if (SSMod[i.modIdx] < 0) calcSSModGred(i.terms)
        #
        #   add to the list of SSMods for the free terms
        i.mod <- SSMod[i.modIdx]
        names(i.mod) <- i
        freeSS <- c(freeSS,i.mod)
      }
    }  
  } else {   #  if forced, used the SSModels calculated at the
    #  above level
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
  #   which is the model which is least significant
  #          
  signf.free <- names(which( freeSS == min(freeSS))[1] )[1] 
  
  
  #   If there are terms after dropping, continue dropping
  #   & forcing terms
  #
  new.terms <- this.terms[-which(this.terms==signf.free)]   
  if ( length(new.terms) >= 1 ) {   # are there terms to drop
    # or force?
    # drop the term first
    findBest(new.terms, this.forced, traceModels = traceModels, terms=terms, notFree=notFree, timeOut=timeOut)    
    #    force the least significant term into the model
    new.forced <- c(this.forced, signf.free)
    new.freeSS <- freeSS[-which(names(freeSS)==signf.free)]
    findBest(this.terms, new.forced, forced=TRUE,
             forced.freeSS=new.freeSS, traceModels = traceModels, terms = terms, notFree=notFree, timeOut=timeOut)     
  }
  
}
