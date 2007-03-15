/* This file was generated by SableCC (http://www.sablecc.org/). */

package src.promela.node;

import src.promela.analysis.*;

@SuppressWarnings("nls")
public final class ACompoundBitandExpr extends PBitandExpr
{
    private PEqExpr _eqExpr_;
    private TBitand _bitand_;
    private PBitandExpr _bitandExpr_;

    public ACompoundBitandExpr()
    {
        // Constructor
    }

    public ACompoundBitandExpr(
        @SuppressWarnings("hiding") PEqExpr _eqExpr_,
        @SuppressWarnings("hiding") TBitand _bitand_,
        @SuppressWarnings("hiding") PBitandExpr _bitandExpr_)
    {
        // Constructor
        setEqExpr(_eqExpr_);

        setBitand(_bitand_);

        setBitandExpr(_bitandExpr_);

    }

    @Override
    public Object clone()
    {
        return new ACompoundBitandExpr(
            cloneNode(this._eqExpr_),
            cloneNode(this._bitand_),
            cloneNode(this._bitandExpr_));
    }

    public void apply(Switch sw)
    {
        ((Analysis) sw).caseACompoundBitandExpr(this);
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

    public TBitand getBitand()
    {
        return this._bitand_;
    }

    public void setBitand(TBitand node)
    {
        if(this._bitand_ != null)
        {
            this._bitand_.parent(null);
        }

        if(node != null)
        {
            if(node.parent() != null)
            {
                node.parent().removeChild(node);
            }

            node.parent(this);
        }

        this._bitand_ = node;
    }

    public PBitandExpr getBitandExpr()
    {
        return this._bitandExpr_;
    }

    public void setBitandExpr(PBitandExpr node)
    {
        if(this._bitandExpr_ != null)
        {
            this._bitandExpr_.parent(null);
        }

        if(node != null)
        {
            if(node.parent() != null)
            {
                node.parent().removeChild(node);
            }

            node.parent(this);
        }

        this._bitandExpr_ = node;
    }

    @Override
    public String toString()
    {
        return ""
            + toString(this._eqExpr_)
            + toString(this._bitand_)
            + toString(this._bitandExpr_);
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

        if(this._bitand_ == child)
        {
            this._bitand_ = null;
            return;
        }

        if(this._bitandExpr_ == child)
        {
            this._bitandExpr_ = null;
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

        if(this._bitand_ == oldChild)
        {
            setBitand((TBitand) newChild);
            return;
        }

        if(this._bitandExpr_ == oldChild)
        {
            setBitandExpr((PBitandExpr) newChild);
            return;
        }

        throw new RuntimeException("Not a child.");
    }
}
