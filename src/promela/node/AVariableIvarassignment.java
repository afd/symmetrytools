/* This file was generated by SableCC (http://www.sablecc.org/). */

package src.promela.node;

import src.promela.analysis.*;

@SuppressWarnings("nls")
public final class AVariableIvarassignment extends PIvarassignment
{
    private TAssign _assign_;
    private PExpr _expr_;

    public AVariableIvarassignment()
    {
        // Constructor
    }

    public AVariableIvarassignment(
        @SuppressWarnings("hiding") TAssign _assign_,
        @SuppressWarnings("hiding") PExpr _expr_)
    {
        // Constructor
        setAssign(_assign_);

        setExpr(_expr_);

    }

    @Override
    public Object clone()
    {
        return new AVariableIvarassignment(
            cloneNode(this._assign_),
            cloneNode(this._expr_));
    }

    public void apply(Switch sw)
    {
        ((Analysis) sw).caseAVariableIvarassignment(this);
    }

    public TAssign getAssign()
    {
        return this._assign_;
    }

    public void setAssign(TAssign node)
    {
        if(this._assign_ != null)
        {
            this._assign_.parent(null);
        }

        if(node != null)
        {
            if(node.parent() != null)
            {
                node.parent().removeChild(node);
            }

            node.parent(this);
        }

        this._assign_ = node;
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

    @Override
    public String toString()
    {
        return ""
            + toString(this._assign_)
            + toString(this._expr_);
    }

    @Override
    void removeChild(@SuppressWarnings("unused") Node child)
    {
        // Remove child
        if(this._assign_ == child)
        {
            this._assign_ = null;
            return;
        }

        if(this._expr_ == child)
        {
            this._expr_ = null;
            return;
        }

        throw new RuntimeException("Not a child.");
    }

    @Override
    void replaceChild(@SuppressWarnings("unused") Node oldChild, @SuppressWarnings("unused") Node newChild)
    {
        // Replace child
        if(this._assign_ == oldChild)
        {
            setAssign((TAssign) newChild);
            return;
        }

        if(this._expr_ == oldChild)
        {
            setExpr((PExpr) newChild);
            return;
        }

        throw new RuntimeException("Not a child.");
    }
}
