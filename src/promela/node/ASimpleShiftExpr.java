/* This file was generated by SableCC (http://www.sablecc.org/). */

package src.promela.node;

import src.promela.analysis.*;

@SuppressWarnings("nls")
public final class ASimpleShiftExpr extends PShiftExpr
{
    private PAddExpr _addExpr_;

    public ASimpleShiftExpr()
    {
        // Constructor
    }

    public ASimpleShiftExpr(
        @SuppressWarnings("hiding") PAddExpr _addExpr_)
    {
        // Constructor
        setAddExpr(_addExpr_);

    }

    @Override
    public Object clone()
    {
        return new ASimpleShiftExpr(
            cloneNode(this._addExpr_));
    }

    public void apply(Switch sw)
    {
        ((Analysis) sw).caseASimpleShiftExpr(this);
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
            + toString(this._addExpr_);
    }

    @Override
    void removeChild(@SuppressWarnings("unused") Node child)
    {
        // Remove child
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
        if(this._addExpr_ == oldChild)
        {
            setAddExpr((PAddExpr) newChild);
            return;
        }

        throw new RuntimeException("Not a child.");
    }
}
