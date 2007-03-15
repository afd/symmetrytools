/* This file was generated by SableCC (http://www.sablecc.org/). */

package src.promela.node;

import src.promela.analysis.*;

@SuppressWarnings("nls")
public final class AParentheseFactor extends PFactor
{
    private TLParenthese _lParenthese_;
    private PExpr _expr_;
    private TRParenthese _rParenthese_;

    public AParentheseFactor()
    {
        // Constructor
    }

    public AParentheseFactor(
        @SuppressWarnings("hiding") TLParenthese _lParenthese_,
        @SuppressWarnings("hiding") PExpr _expr_,
        @SuppressWarnings("hiding") TRParenthese _rParenthese_)
    {
        // Constructor
        setLParenthese(_lParenthese_);

        setExpr(_expr_);

        setRParenthese(_rParenthese_);

    }

    @Override
    public Object clone()
    {
        return new AParentheseFactor(
            cloneNode(this._lParenthese_),
            cloneNode(this._expr_),
            cloneNode(this._rParenthese_));
    }

    public void apply(Switch sw)
    {
        ((Analysis) sw).caseAParentheseFactor(this);
    }

    public TLParenthese getLParenthese()
    {
        return this._lParenthese_;
    }

    public void setLParenthese(TLParenthese node)
    {
        if(this._lParenthese_ != null)
        {
            this._lParenthese_.parent(null);
        }

        if(node != null)
        {
            if(node.parent() != null)
            {
                node.parent().removeChild(node);
            }

            node.parent(this);
        }

        this._lParenthese_ = node;
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

    public TRParenthese getRParenthese()
    {
        return this._rParenthese_;
    }

    public void setRParenthese(TRParenthese node)
    {
        if(this._rParenthese_ != null)
        {
            this._rParenthese_.parent(null);
        }

        if(node != null)
        {
            if(node.parent() != null)
            {
                node.parent().removeChild(node);
            }

            node.parent(this);
        }

        this._rParenthese_ = node;
    }

    @Override
    public String toString()
    {
        return ""
            + toString(this._lParenthese_)
            + toString(this._expr_)
            + toString(this._rParenthese_);
    }

    @Override
    void removeChild(@SuppressWarnings("unused") Node child)
    {
        // Remove child
        if(this._lParenthese_ == child)
        {
            this._lParenthese_ = null;
            return;
        }

        if(this._expr_ == child)
        {
            this._expr_ = null;
            return;
        }

        if(this._rParenthese_ == child)
        {
            this._rParenthese_ = null;
            return;
        }

        throw new RuntimeException("Not a child.");
    }

    @Override
    void replaceChild(@SuppressWarnings("unused") Node oldChild, @SuppressWarnings("unused") Node newChild)
    {
        // Replace child
        if(this._lParenthese_ == oldChild)
        {
            setLParenthese((TLParenthese) newChild);
            return;
        }

        if(this._expr_ == oldChild)
        {
            setExpr((PExpr) newChild);
            return;
        }

        if(this._rParenthese_ == oldChild)
        {
            setRParenthese((TRParenthese) newChild);
            return;
        }

        throw new RuntimeException("Not a child.");
    }
}
