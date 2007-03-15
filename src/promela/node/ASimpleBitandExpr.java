/* This file was generated by SableCC (http://www.sablecc.org/). */

package src.promela.node;

import src.promela.analysis.*;

@SuppressWarnings("nls")
public final class ASimpleBitandExpr extends PBitandExpr
{
    private PEqExpr _eqExpr_;

    public ASimpleBitandExpr()
    {
        // Constructor
    }

    public ASimpleBitandExpr(
        @SuppressWarnings("hiding") PEqExpr _eqExpr_)
    {
        // Constructor
        setEqExpr(_eqExpr_);

    }

    @Override
    public Object clone()
    {
        return new ASimpleBitandExpr(
            cloneNode(this._eqExpr_));
    }

    public void apply(Switch sw)
    {
        ((Analysis) sw).caseASimpleBitandExpr(this);
    }

    public PEqExpr getEqExpr()
    {
        return this._eqExpr_;
    }

    public void setEqExpr(PEqExpr node)
    {
        if(this._eqExpr_ != null)
        {
            this._eqExpr_.parent(null);
        }

        if(node != null)
        {
            if(node.parent() != null)
            {
                node.parent().removeChild(node);
            }

            node.parent(this);
        }

        this._eqExpr_ = node;
    }

    @Override
    public String toString()
    {
        return ""
            + toString(this._eqExpr_);
    }

    @Override
    void removeChild(@SuppressWarnings("unused") Node child)
    {
        // Remove child
        if(this._eqExpr_ == child)
        {
            this._eqExpr_ = null;
            return;
        }

        throw new RuntimeException("Not a child.");
    }

    @Override
    void replaceChild(@SuppressWarnings("unused") Node oldChild, @SuppressWarnings("unused") Node newChild)
    {
        // Replace child
        if(this._eqExpr_ == oldChild)
        {
            setEqExpr((PEqExpr) newChild);
            return;
        }

        throw new RuntimeException("Not a child.");
    }
}
