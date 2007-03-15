/* This file was generated by SableCC (http://www.sablecc.org/). */

package src.promela.node;

import src.promela.analysis.*;

@SuppressWarnings("nls")
public final class AManyExprLst extends PExprLst
{
    private PExpr _expr_;
    private TComma _comma_;
    private PExprLst _exprLst_;

    public AManyExprLst()
    {
        // Constructor
    }

    public AManyExprLst(
        @SuppressWarnings("hiding") PExpr _expr_,
        @SuppressWarnings("hiding") TComma _comma_,
        @SuppressWarnings("hiding") PExprLst _exprLst_)
    {
        // Constructor
        setExpr(_expr_);

        setComma(_comma_);

        setExprLst(_exprLst_);

    }

    @Override
    public Object clone()
    {
        return new AManyExprLst(
            cloneNode(this._expr_),
            cloneNode(this._comma_),
            cloneNode(this._exprLst_));
    }

    public void apply(Switch sw)
    {
        ((Analysis) sw).caseAManyExprLst(this);
    }

    public PExpr getExpr()
    {
        return this._expr_;
    }

    public void setExpr(PExpr node)
    {
        if(this._expr_ != null)
        {
            this._expr_.parent(null);
        }

        if(node != null)
        {
            if(node.parent() != null)
            {
                node.parent().removeChild(node);
            }

            node.parent(this);
        }

        this._expr_ = node;
    }

    public TComma getComma()
    {
        return this._comma_;
    }

    public void setComma(TComma node)
    {
        if(this._comma_ != null)
        {
            this._comma_.parent(null);
        }

        if(node != null)
        {
            if(node.parent() != null)
            {
                node.parent().removeChild(node);
            }

            node.parent(this);
        }

        this._comma_ = node;
    }

    public PExprLst getExprLst()
    {
        return this._exprLst_;
    }

    public void setExprLst(PExprLst node)
    {
        if(this._exprLst_ != null)
        {
            this._exprLst_.parent(null);
        }

        if(node != null)
        {
            if(node.parent() != null)
            {
                node.parent().removeChild(node);
            }

            node.parent(this);
        }

        this._exprLst_ = node;
    }

    @Override
    public String toString()
    {
        return ""
            + toString(this._expr_)
            + toString(this._comma_)
            + toString(this._exprLst_);
    }

    @Override
    void removeChild(@SuppressWarnings("unused") Node child)
    {
        // Remove child
        if(this._expr_ == child)
        {
            this._expr_ = null;
            return;
        }

        if(this._comma_ == child)
        {
            this._comma_ = null;
            return;
        }

        if(this._exprLst_ == child)
        {
            this._exprLst_ = null;
            return;
        }

        throw new RuntimeException("Not a child.");
    }

    @Override
    void replaceChild(@SuppressWarnings("unused") Node oldChild, @SuppressWarnings("unused") Node newChild)
    {
        // Replace child
        if(this._expr_ == oldChild)
        {
            setExpr((PExpr) newChild);
            return;
        }

        if(this._comma_ == oldChild)
        {
            setComma((TComma) newChild);
            return;
        }

        if(this._exprLst_ == oldChild)
        {
            setExprLst((PExprLst) newChild);
            return;
        }

        throw new RuntimeException("Not a child.");
    }
}
