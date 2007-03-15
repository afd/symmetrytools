/* This file was generated by SableCC (http://www.sablecc.org/). */

package src.promela.node;

import src.promela.analysis.*;

@SuppressWarnings("nls")
public final class ACompoundBitxorExpr extends PBitxorExpr
{
    private PBitandExpr _bitandExpr_;
    private TBitxor _bitxor_;
    private PBitxorExpr _bitxorExpr_;

    public ACompoundBitxorExpr()
    {
        // Constructor
    }

    public ACompoundBitxorExpr(
        @SuppressWarnings("hiding") PBitandExpr _bitandExpr_,
        @SuppressWarnings("hiding") TBitxor _bitxor_,
        @SuppressWarnings("hiding") PBitxorExpr _bitxorExpr_)
    {
        // Constructor
        setBitandExpr(_bitandExpr_);

        setBitxor(_bitxor_);

        setBitxorExpr(_bitxorExpr_);

    }

    @Override
    public Object clone()
    {
        return new ACompoundBitxorExpr(
            cloneNode(this._bitandExpr_),
            cloneNode(this._bitxor_),
            cloneNode(this._bitxorExpr_));
    }

    public void apply(Switch sw)
    {
        ((Analysis) sw).caseACompoundBitxorExpr(this);
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

    public TBitxor getBitxor()
    {
        return this._bitxor_;
    }

    public void setBitxor(TBitxor node)
    {
        if(this._bitxor_ != null)
        {
            this._bitxor_.parent(null);
        }

        if(node != null)
        {
            if(node.parent() != null)
            {
                node.parent().removeChild(node);
            }

            node.parent(this);
        }

        this._bitxor_ = node;
    }

    public PBitxorExpr getBitxorExpr()
    {
        return this._bitxorExpr_;
    }

    public void setBitxorExpr(PBitxorExpr node)
    {
        if(this._bitxorExpr_ != null)
        {
            this._bitxorExpr_.parent(null);
        }

        if(node != null)
        {
            if(node.parent() != null)
            {
                node.parent().removeChild(node);
            }

            node.parent(this);
        }

        this._bitxorExpr_ = node;
    }

    @Override
    public String toString()
    {
        return ""
            + toString(this._bitandExpr_)
            + toString(this._bitxor_)
            + toString(this._bitxorExpr_);
    }

    @Override
    void removeChild(@SuppressWarnings("unused") Node child)
    {
        // Remove child
        if(this._bitandExpr_ == child)
        {
            this._bitandExpr_ = null;
            return;
        }

        if(this._bitxor_ == child)
        {
            this._bitxor_ = null;
            return;
        }

        if(this._bitxorExpr_ == child)
        {
            this._bitxorExpr_ = null;
            return;
        }

        throw new RuntimeException("Not a child.");
    }

    @Override
    void replaceChild(@SuppressWarnings("unused") Node oldChild, @SuppressWarnings("unused") Node newChild)
    {
        // Replace child
        if(this._bitandExpr_ == oldChild)
        {
            setBitandExpr((PBitandExpr) newChild);
            return;
        }

        if(this._bitxor_ == oldChild)
        {
            setBitxor((TBitxor) newChild);
            return;
        }

        if(this._bitxorExpr_ == oldChild)
        {
            setBitxorExpr((PBitxorExpr) newChild);
            return;
        }

        throw new RuntimeException("Not a child.");
    }
}
