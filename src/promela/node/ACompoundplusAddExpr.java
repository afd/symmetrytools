/* This file was generated by SableCC (http://www.sablecc.org/). */

package src.promela.node;

import src.promela.analysis.*;

@SuppressWarnings("nls")
public final class ACompoundplusAddExpr extends PAddExpr
{
    private PMultExpr _multExpr_;
    private TPlus _plus_;
    private PAddExpr _addExpr_;

    public ACompoundplusAddExpr()
    {
        // Constructor
    }

    public ACompoundplusAddExpr(
        @SuppressWarnings("hiding") PMultExpr _multExpr_,
        @SuppressWarnings("hiding") TPlus _plus_,
        @SuppressWarnings("hiding") PAddExpr _addExpr_)
    {
        // Constructor
        setMultExpr(_multExpr_);

        setPlus(_plus_);

        setAddExpr(_addExpr_);

    }

    @Override
    public Object clone()
    {
        return new ACompoundplusAddExpr(
            cloneNode(this._multExpr_),
            cloneNode(this._plus_),
            cloneNode(this._addExpr_));
    }

    public void apply(Switch sw)
    {
        ((Analysis) sw).caseACompoundplusAddExpr(this);
    }

    public PMultExpr getMultExpr()
    {
        return this._multExpr_;
    }

    public void setMultExpr(PMultExpr node)
    {
        if(this._multExpr_ != null)
        {
            this._multExpr_.parent(null);
        }

        if(node != null)
        {
            if(node.parent() != null)
            {
                node.parent().removeChild(node);
            }

            node.parent(this);
        }

        this._multExpr_ = node;
    }

    public TPlus getPlus()
    {
        return this._plus_;
    }

    public void setPlus(TPlus node)
    {
        if(this._plus_ != null)
        {
            this._plus_.parent(null);
        }

        if(node != null)
        {
            if(node.parent() != null)
            {
                node.parent().removeChild(node);
            }

            node.parent(this);
        }

        this._plus_ = node;
    }

    public PAddExpr getAddExpr()
    {
        return this._addExpr_;
    }

    public void setAddExpr(PAddExpr node)
    {
        if(this._addExpr_ != null)
        {
            this._addExpr_.parent(null);
        }

        if(node != null)
        {
            if(node.parent() != null)
            {
                node.parent().removeChild(node);
            }

            node.parent(this);
        }

        this._addExpr_ = node;
    }

    @Override
    public String toString()
    {
        return ""
            + toString(this._multExpr_)
            + toString(this._plus_)
            + toString(this._addExpr_);
    }

    @Override
    void removeChild(@SuppressWarnings("unused") Node child)
    {
        // Remove child
        if(this._multExpr_ == child)
        {
            this._multExpr_ = null;
            return;
        }

        if(this._plus_ == child)
        {
            this._plus_ = null;
            return;
        }

        if(this._addExpr_ == child)
        {
            this._addExpr_ = null;
            return;
        }

        throw new RuntimeException("Not a child.");
    }

    @Override
    void replaceChild(@SuppressWarnings("unused") Node oldChild, @SuppressWarnings("unused") Node newChild)
    {
        // Replace child
        if(this._multExpr_ == oldChild)
        {
            setMultExpr((PMultExpr) newChild);
            return;
        }

        if(this._plus_ == oldChild)
        {
            setPlus((TPlus) newChild);
            return;
        }

        if(this._addExpr_ == oldChild)
        {
            setAddExpr((PAddExpr) newChild);
            return;
        }

        throw new RuntimeException("Not a child.");
    }
}
